// Streams the real world around the car: OSM data → ground texture, buildings, trees, colliders.
import {clamp,lerp,hash,rng} from './util.js';
import {toLocal,toLatLon,demAt,fetchOSM,ensureElev} from './geo.js';

const THREE=window.THREE;
export const CH=400;            // chunk size in metres
const HG=8,HN=CH/HG+1;          // height grid spacing / samples per side
const MOBILE=matchMedia('(pointer:coarse)').matches;
const TEX=MOBILE?768:1024;      // ground texture px per chunk
const S=TEX/CH;                 // px per metre
const BUILD_R=1,FETCH_R=2,DROP_R=3;

/* ---------------- state ---------------- */
let scene=null,renderer=null,root=null,gen=0,abort=null;
export const W={h0:0,ready:false,status:'',busy:0,error:null};
let ways=new Map(),rels=new Map(),treeNodes=new Map();
let chunks=new Map(),roadGrid=new Map(),colGrid=new Map();
let fetchQ=[],fetching=0,buildQ=[];
const RG=32,CG=16;

export function initWorld(sc,rd){scene=sc;renderer=rd}

/* ---------------- classification ---------------- */
const ROAD={
  motorway:[12,9,'#55565a'],trunk:[10,8,'#535458'],primary:[9,7,'#4f5054'],secondary:[8,6,'#4f5054'],tertiary:[7,5,'#4e4f53'],
  motorway_link:[6,4,'#55565a'],trunk_link:[6,4,'#535458'],primary_link:[6,4,'#4f5054'],secondary_link:[5.5,4,'#4f5054'],tertiary_link:[5,4,'#4e4f53'],
  residential:[6,3,'#4d4e52'],living_street:[5,3,'#59575a'],unclassified:[5.5,3,'#4d4e52'],road:[6,3,'#4d4e52'],busway:[6,3,'#4d4e52'],
  service:[4,2,'#4f5054'],track:[3.2,1,'#a8976f'],pedestrian:[5,2,'#b9b0a0'],raceway:[10,6,'#46474b'],
};
const PATH={footway:1.8,path:1.6,cycleway:2.2,bridleway:1.8,steps:1.8,corridor:0};
const UNPAVED=/^(unpaved|gravel|fine_gravel|dirt|earth|ground|grass|compacted|sand|mud|pebblestone|wood|grass_paver)$/;
const NAMES={track:'Feldweg',service:'Zufahrt',footway:'Fußweg',cycleway:'Radweg',path:'Weg',pedestrian:'Fußgängerzone',motorway:'Autobahn',motorway_link:'Auffahrt',living_street:'Spielstraße'};

function areaStyle(t){
  const L=t.landuse,Nn=t.natural,Le=t.leisure;
  if(t.amenity==='parking'||t['area:highway']||(t.highway&&t.area==='yes'))return t.highway==='pedestrian'||t['area:highway']==='footway'?{c:'#bdb4a3',p:5,s:2}:{c:'#6f7074',p:5,s:2,park:1};
  if(Nn==='water'||t.water||L==='reservoir'||L==='basin'||t.waterway==='riverbank'||t.waterway==='dock')return {c:'#4b7ea0',p:4,s:3,water:1};
  if(Le){const m={park:['#86b45a',3],garden:['#8bb763',3],pitch:['#5f9e47',3],playground:['#b8c48f',3],golf_course:['#8cc464',3],stadium:['#a9a49b',3],track:['#b5674d',3],sports_centre:['#b9b4ab',3],swimming_pool:['#5aa7c9',4],nature_reserve:null,dog_park:['#9cbc72',3],marina:['#4b7ea0',4],common:['#93b55e',3]}[Le];if(m)return {c:m[0],p:m[1],pitch:Le==='pitch',s:Le==='swimming_pool'||Le==='marina'?3:0}}
  if(L==='forest'||Nn==='wood')return {c:'#46693a',p:2,forest:1,needle:t.leaf_type==='needleleaved'};
  const lu={residential:'#a9b488',commercial:'#c7bfb6',retail:'#c9beb4',industrial:'#b9b3aa',railway:'#b4ada2',military:'#b9b29d',brownfield:'#b9ad93',construction:'#bfae90',garages:'#a9a6a1',education:'#cdc4b0',religious:'#c9c2b2',landfill:'#a89f8a',
    farmland:'#cdbf86',farmyard:'#bfaf8c',meadow:'#98b862',grass:'#92b45e',village_green:'#8fb65c',recreation_ground:'#93b75f',orchard:'#86a755',vineyard:'#a6ad63',allotments:'#a3b872',cemetery:'#8fa877',greenhouse_horticulture:'#c7ccc0',plant_nursery:'#9fb874',quarry:'#b8b0a2',flowerbed:'#a3b46e'}[L];
  if(lu){const nat=/^(farmland|meadow|grass|village_green|recreation_ground|orchard|vineyard|allotments|cemetery|plant_nursery|flowerbed)$/.test(L);return {c:lu,p:nat?1:0,farm:L==='farmland',orchard:L==='orchard'}}
  const nm={scrub:'#7f9c55',heath:'#a7a56c',grassland:'#9cb766',sand:'#dccfa0',beach:'#e0d3a2',wetland:'#7da187',bare_rock:'#a7a39b',scree:'#b0aba1',glacier:'#e8eef2'}[Nn];
  if(nm)return {c:nm,p:1};
  return null;
}
function bbOf(pts){let a=1e9,b=1e9,c=-1e9,d=-1e9;for(const p of pts){if(p[0]<a)a=p[0];if(p[1]<b)b=p[1];if(p[0]>c)c=p[0];if(p[1]>d)d=p[1]}return [a,b,c,d]}
function areaOf(r){let s=0;for(let i=0,n=r.length;i<n;i++){const p=r[i],q=r[(i+1)%n];s+=p[0]*q[1]-q[0]*p[1]}return s/2}
const eqp=(a,b)=>Math.abs(a[0]-b[0])<.05&&Math.abs(a[1]-b[1])<.05;
function isClosed(p){return p.length>3&&eqp(p[0],p[p.length-1])}
function parseNum(v){if(v==null)return NaN;const m=String(v).replace(',','.').match(/-?\d+(\.\d+)?/);return m?parseFloat(m[0]):NaN}

function classify(o){
  const t=o.tags;
  if(t.building&&t.building!=='no'){
    if(t.location==='underground'||+t.layer<0||t.building==='roof'||t.building==='carport'||t.building==='construction'&&!t['building:levels'])return null;
    const rings=o.rings||(isClosed(o.pts)?{outer:[o.pts],inner:[]}:null);if(!rings||!rings.outer.length)return null;
    return {...o,kind:'bld',rings};
  }
  if(t.highway&&!(t.area==='yes')){
    if(t.tunnel&&t.tunnel!=='no'&&t.tunnel!=='building_passage')return null;
    if(+t.layer<0&&t.highway!=='motorway')return null;
    const r=ROAD[t.highway];
    if(r){let w=parseNum(t.width);const lanes=parseNum(t.lanes);if(!(w>2))w=r[0];if(lanes>0)w=Math.max(w,lanes*3.1);w=clamp(w,2.5,30);
      const unp=t.highway==='track'?!(t.surface&&!UNPAVED.test(t.surface)):UNPAVED.test(t.surface||'');
      return {...o,kind:'road',w,rank:r[1],col:unp?'#a8976f':r[2],unp,oneway:t.oneway==='yes'||t.highway==='motorway'||t.junction==='roundabout',lanes:lanes>0?lanes:0}}
    const pw=PATH[t.highway];if(pw)return {...o,kind:'path',w:pw};
    return null;
  }
  if(t.railway){if(t.tunnel&&t.tunnel!=='no')return null;return {...o,kind:'rail',tram:t.railway==='tram'}}
  if(t.waterway&&!o.rings&&!isClosed(o.pts)){if(t.tunnel)return null;const w={river:14,canal:12,stream:3,brook:2.5,ditch:1.5,drain:1.5}[t.waterway];if(!w)return null;let ww=parseNum(t.width);return {...o,kind:'wline',w:ww>0?ww:w}}
  if(t.natural==='tree_row')return {...o,kind:'trow'};
  const st=areaStyle(t);
  if(st){const rings=o.rings||(isClosed(o.pts)?{outer:[o.pts],inner:[]}:null);if(!rings||!rings.outer.length)return null;
    return {...o,kind:'area',st,rings,size:Math.abs(rings.outer.reduce((s,r)=>s+areaOf(r),0))}}
  return null;
}
function stitch(members){
  const out={outer:[],inner:[]};
  for(const role of ['outer','inner']){
    const pool=members.filter(m=>m.type==='way'&&m.geometry&&((m.role==='inner')===(role==='inner'))).map(m=>m.geometry.filter(Boolean).map(g=>toLocal(g.lat,g.lon))).filter(p=>p.length>1);
    while(pool.length){
      let ring=pool.shift();let guard=0;
      while(!isClosed(ring)&&guard++<400){
        const end=ring[ring.length-1];let f=-1,rev=false;
        for(let i=0;i<pool.length;i++){const p=pool[i];if(eqp(p[0],end)){f=i;break}if(eqp(p[p.length-1],end)){f=i;rev=true;break}}
        if(f<0)break;let p=pool.splice(f,1)[0];if(rev)p=p.slice().reverse();ring=ring.concat(p.slice(1));
      }
      if(ring.length>=3)out[role].push(ring);
    }
  }
  return out;
}
function ingest(els){
  for(const e of els){
    if(e.type==='node'){if(!treeNodes.has(e.id)&&e.lat!=null){const [x,z]=toLocal(e.lat,e.lon);treeNodes.set(e.id,{x,z,t:e.tags||{}})}continue}
    if(e.type==='way'){
      if(ways.has(e.id)||!e.geometry)continue;
      const pts=e.geometry.filter(Boolean).map(g=>toLocal(g.lat,g.lon));if(pts.length<2)continue;
      const w=classify({id:e.id,tags:e.tags||{},pts});if(!w)continue;
      w.bb=bbOf(w.rings?w.rings.outer.flat():pts);ways.set(e.id,w);
      if(w.kind==='road')indexRoad(w);
      if(w.kind==='bld')prepBuilding(w);
    }else if(e.type==='relation'){
      if(rels.has(e.id)||!e.members)continue;
      const rings=stitch(e.members);if(!rings.outer.length)continue;
      const r=classify({id:-e.id,tags:e.tags||{},pts:rings.outer[0],rings});if(!r)continue;
      r.bb=bbOf(rings.outer.flat());rels.set(e.id,r);
      if(r.kind==='bld')prepBuilding(r);
    }
  }
}
function prepBuilding(b){
  let cx=0,cz=0,n=0;for(const p of b.rings.outer[0]){cx+=p[0];cz+=p[1];n++}b.cx=cx/n;b.cz=cz/n;
  b.size=Math.abs(b.rings.outer.reduce((s,r)=>s+areaOf(r),0));
}
function indexRoad(w){
  const p=w.pts;
  for(let k=0;k<p.length-1;k++){
    const a=p[k],b=p[k+1];
    const i0=Math.floor(Math.min(a[0],b[0])/RG),i1=Math.floor(Math.max(a[0],b[0])/RG),j0=Math.floor(Math.min(a[1],b[1])/RG),j1=Math.floor(Math.max(a[1],b[1])/RG);
    for(let i=i0;i<=i1;i++)for(let j=j0;j<=j1;j++){const key=i+','+j;let c=roadGrid.get(key);if(!c)roadGrid.set(key,c=[]);c.push([w,k])}
  }
}
export function nearestRoad(x,z,R=60,pred){
  let best=null,bd=R*R;
  const i0=Math.floor((x-R)/RG),i1=Math.floor((x+R)/RG),j0=Math.floor((z-R)/RG),j1=Math.floor((z+R)/RG);
  for(let i=i0;i<=i1;i++)for(let j=j0;j<=j1;j++){const c=roadGrid.get(i+','+j);if(!c)continue;
    for(const [w,k] of c){if(pred&&!pred(w))continue;const a=w.pts[k],b=w.pts[k+1];const dx=b[0]-a[0],dz=b[1]-a[1],l2=dx*dx+dz*dz||1;
      const t=clamp(((x-a[0])*dx+(z-a[1])*dz)/l2,0,1),px=a[0]+dx*t,pz=a[1]+dz*t,d=(px-x)**2+(pz-z)**2;
      if(d<bd){bd=d;const l=Math.sqrt(l2);best={w,x:px,z:pz,dx:dx/l,dz:dz/l,d:Math.sqrt(d)}}}}
  return best;
}
export function placeName(x,z){
  const r=nearestRoad(x,z,22,w=>w.tags.name);
  if(r)return r.w.tags.name;
  const q=nearestRoad(x,z,12);
  if(q)return q.w.tags.ref||NAMES[q.w.tags.highway]||'Straße';
  return null;
}

/* ---------------- heights & surface ---------------- */
const SAMP=[[0,0],[6,0],[-6,0],[0,6],[0,-6]];
function demLocal(x,z){let s=0,n=0;for(const [dx,dz] of SAMP){const [la,lo]=toLatLon(x+dx,z+dz),v=demAt(la,lo);if(v!=null){s+=v;n++}}return n?s/n:null}
function rawH(x,z){const v=demLocal(x,z);return v==null?0:v-W.h0}
function chunkAt(x,z){return chunks.get(Math.round(x/CH)+','+Math.round(z/CH))}
export function height(x,z){
  const c=chunkAt(x,z);
  if(c&&c.h){const lx=(x-c.x0)/HG,lz=(z-c.z0)/HG,ix=clamp(Math.floor(lx),0,HN-2),iz=clamp(Math.floor(lz),0,HN-2),fx=lx-ix,fz=lz-iz,k=iz*HN+ix,h=c.h;
    return (h[k]*(1-fx)+h[k+1]*fx)*(1-fz)+(h[k+HN]*(1-fx)+h[k+HN+1]*fx)*fz}
  return rawH(x,z);
}
// 0 grass/ground, 1 gravel, 2 asphalt/paving, 3 water
export function surfaceAt(x,z){
  const c=chunkAt(x,z);if(!c||!c.surf)return 2;
  const i=clamp(Math.floor(x-c.x0),0,CH-1),j=clamp(Math.floor(z-c.z0),0,CH-1);return c.surf[j*CH+i];
}
function computeHeights(c){
  const h=new Float32Array(HN*HN);
  for(let j=0;j<HN;j++)for(let i=0;i<HN;i++)h[j*HN+i]=rawH(c.x0+i*HG,c.z0+j*HG);
  c.h=h;
}

/* ---------------- colliders ---------------- */
function addCol(c,ck,cells){
  const x0=c.t?c.x-c.r:Math.min(c.x1,c.x2),x1=c.t?c.x+c.r:Math.max(c.x1,c.x2),z0=c.t?c.z-c.r:Math.min(c.z1,c.z2),z1=c.t?c.z+c.r:Math.max(c.z1,c.z2);
  c.ck=ck;
  for(let i=Math.floor(x0/CG);i<=Math.floor(x1/CG);i++)for(let j=Math.floor(z0/CG);j<=Math.floor(z1/CG);j++){const k=i+','+j;let a=colGrid.get(k);if(!a){colGrid.set(k,a=[]);}a.push(c);cells.add(k)}
}
export function collidersNear(x,z,out){
  out.length=0;const ci=Math.floor(x/CG),cj=Math.floor(z/CG);
  for(let i=ci-1;i<=ci+1;i++)for(let j=cj-1;j<=cj+1;j++){const a=colGrid.get(i+','+j);if(a)for(const c of a)out.push(c)}
  return out;
}
// first building wall hit between (ax,az)->(bx,bz) below height y; returns fraction or 1
export function rayWalls(ax,az,bx,bz,y){
  let best=1;const steps=Math.ceil(Math.hypot(bx-ax,bz-az)/CG)+1,seen=new Set();
  for(let s=0;s<=steps;s++){const x=lerp(ax,bx,s/steps),z=lerp(az,bz,s/steps),k=Math.floor(x/CG)+','+Math.floor(z/CG);if(seen.has(k))continue;seen.add(k);
    const a=colGrid.get(k);if(!a)continue;
    for(const c of a){if(c.t||!(c.top>y))continue;
      const rx=bx-ax,rz=bz-az,sx=c.x2-c.x1,sz=c.z2-c.z1,den=rx*sz-rz*sx;if(Math.abs(den)<1e-9)continue;
      const t=((c.x1-ax)*sz-(c.z1-az)*sx)/den,u=((c.x1-ax)*rz-(c.z1-az)*rx)/den;if(t>0&&t<best&&u>=0&&u<=1)best=t}}
  return best;
}

/* ---------------- shared materials & textures ---------------- */
let MAT=null;
function canvasTex(w,h,draw,rep){const c=document.createElement('canvas');c.width=w;c.height=h;draw(c.getContext('2d'),w,h);const t=new THREE.CanvasTexture(c);t.anisotropy=Math.min(8,renderer.capabilities.getMaxAnisotropy());if(rep)t.wrapS=t.wrapT=THREE.RepeatWrapping;return t}
function grain(g,w,h,base,amt){g.fillStyle=base;g.fillRect(0,0,w,h);const d=g.getImageData(0,0,w,h);for(let i=0;i<d.data.length;i+=4){const n=(Math.random()-.5)*amt;d.data[i]+=n;d.data[i+1]+=n;d.data[i+2]+=n}g.putImageData(d,0,0)}
const PAT={};
function patterns(){
  const mk=(w,h,f)=>{const c=document.createElement('canvas');c.width=w;c.height=h;f(c.getContext('2d'),w,h);return c};
  PAT.noise=mk(128,128,(g,w,h)=>{const d=g.createImageData(w,h);for(let i=0;i<d.data.length;i+=4){const v=Math.random()*255;d.data[i]=d.data[i+1]=d.data[i+2]=v;d.data[i+3]=255}g.putImageData(d,0,0)});
  PAT.canopy=mk(96,96,(g,w,h)=>{g.clearRect(0,0,w,h);for(let k=0;k<160;k++){const x=Math.random()*w,y=Math.random()*h,r=1.4+Math.random()*2.6;g.fillStyle=Math.random()<.5?'rgba(20,40,15,.35)':'rgba(140,170,90,.22)';for(const ox of [-w,0,w])for(const oy of [-h,0,h]){g.beginPath();g.arc(x+ox,y+oy,r,0,7);g.fill()}}});
  PAT.stripe=mk(8,8,(g,w,h)=>{g.clearRect(0,0,w,h);g.fillStyle='rgba(90,70,30,.16)';g.fillRect(0,0,w,3)});
  PAT.orch=mk(8,8,(g,w,h)=>{g.clearRect(0,0,w,h);g.fillStyle='rgba(40,70,25,.55)';g.beginPath();g.arc(4,4,2.2,0,7);g.fill()});
}
function initShared(){
  if(MAT)return;
  patterns();
  const win=canvasTex(256,256,(g,w,h)=>{
    grain(g,w,h,'#ffffff',12);const T=w/4;
    for(let i=0;i<4;i++)for(let j=0;j<4;j++){const x=i*T,y=j*T;
      g.fillStyle='#2b3440';g.fillRect(x+T*.22,y+T*.2,T*.56,T*.56);
      if(Math.random()<.35){g.fillStyle='rgba(160,185,210,.35)';g.fillRect(x+T*.24,y+T*.22,T*.22,T*.52)}
      if(Math.random()<.1){g.fillStyle='rgba(255,214,140,.5)';g.fillRect(x+T*.24,y+T*.22,T*.52,T*.52)}
      g.fillStyle='rgba(255,255,255,.4)';g.fillRect(x+T*.49,y+T*.2,T*.02,T*.56);g.fillStyle='rgba(0,0,0,.18)';g.fillRect(x+T*.2,y+T*.76,T*.6,T*.04)}
    g.fillStyle='#fff';g.fillRect(0,0,6,6);
  },true);
  MAT={
    bld:new THREE.MeshLambertMaterial({map:win,vertexColors:true}),
    trunk:new THREE.MeshLambertMaterial({color:'#4a3626'}),
    con:new THREE.MeshLambertMaterial({color:'#ffffff'}),
    broad:new THREE.MeshLambertMaterial({color:'#ffffff'}),
    trunkG:(()=>{const g=new THREE.CylinderGeometry(.16,.26,1,6);g.translate(0,.5,0);return g})(),
    conG:(()=>{const g=new THREE.ConeGeometry(1.9,1,7);g.translate(0,.5,0);return g})(),
    broadG:new THREE.IcosahedronGeometry(1,1),
  };
  MAT.base=new THREE.Mesh(new THREE.PlaneGeometry(9000,9000),new THREE.MeshLambertMaterial({color:'#93a96a'}));
  MAT.base.rotation.x=-Math.PI/2;MAT.base.receiveShadow=true;
}

/* ---------------- ground texture ---------------- */
function tracePoly(g,rings){g.beginPath();for(const r of [...rings.outer,...rings.inner]){r.forEach((p,i)=>i?g.lineTo(p[0],p[1]):g.moveTo(p[0],p[1]));g.closePath()}}
function traceLine(g,pts){g.beginPath();pts.forEach((p,i)=>i?g.lineTo(p[0],p[1]):g.moveTo(p[0],p[1]))}
function offsetLine(pts,d){return pts.map((p,i)=>{const a=pts[Math.max(0,i-1)],b=pts[Math.min(pts.length-1,i+1)];let tx=b[0]-a[0],tz=b[1]-a[1];const l=Math.hypot(tx,tz)||1;return [p[0]-tz/l*d,p[1]+tx/l*d]})}
const inter=(a,b)=>!(a[2]<b[0]||a[0]>b[2]||a[3]<b[1]||a[1]>b[3]);

function drawGround(c,items){
  const cv=document.createElement('canvas');cv.width=cv.height=TEX;
  const g=cv.getContext('2d');
  const mk=document.createElement('canvas');mk.width=mk.height=CH;
  const m=mk.getContext('2d',{willReadFrequently:true});
  g.fillStyle='#9fb273';g.fillRect(0,0,TEX,TEX);
  g.globalAlpha=.18;g.fillStyle=g.createPattern(PAT.noise,'repeat');g.save();g.scale(3,3);g.fillRect(0,0,TEX,TEX);g.restore();g.globalAlpha=1;
  m.fillStyle='#000';m.fillRect(0,0,CH,CH);
  g.setTransform(S,0,0,S,-c.x0*S,-c.z0*S);m.setTransform(1,0,0,1,-c.x0,-c.z0);
  g.lineCap=m.lineCap='round';g.lineJoin=m.lineJoin='round';
  const areas=items.filter(o=>o.kind==='area').sort((a,b)=>a.st.p-b.st.p||b.size-a.size);
  for(const a of areas){
    tracePoly(g,a.rings);g.fillStyle=a.st.c;g.fill('evenodd');
    if(a.st.forest){const p=g.createPattern(PAT.canopy,'repeat');g.fillStyle=p;g.fill('evenodd')}
    if(a.st.farm){const p=g.createPattern(PAT.stripe,'repeat');try{p.setTransform(new DOMMatrix().rotate(hash(a.id)*180).scale(1.2))}catch(e){}g.fillStyle=p;g.fill('evenodd')}
    if(a.st.orchard){const p=g.createPattern(PAT.orch,'repeat');g.fillStyle=p;g.fill('evenodd')}
    if(a.st.pitch){g.save();g.clip('evenodd');g.strokeStyle='rgba(255,255,255,.7)';g.lineWidth=.25;const r=a.rings.outer[0];traceLine(g,r);g.stroke();g.restore()}
    if(a.st.water){g.strokeStyle='rgba(30,60,80,.35)';g.lineWidth=.8;g.stroke()}
    if(a.st.s){tracePoly(m,a.rings);m.fillStyle=a.st.s===3?'#0000ff':'#ff0000';m.fill('evenodd')}
  }
  const wl=items.filter(o=>o.kind==='wline');
  for(const w of wl){traceLine(g,w.pts);g.strokeStyle='#4b7ea0';g.lineWidth=w.w;g.stroke();traceLine(m,w.pts);m.strokeStyle='#0000ff';m.lineWidth=w.w;m.stroke()}
  const paths=items.filter(o=>o.kind==='path');
  for(const p of paths){traceLine(g,p.pts);g.strokeStyle='#d3c9b6';g.lineWidth=p.w;g.stroke();traceLine(m,p.pts);m.strokeStyle='#00ff00';m.lineWidth=p.w;m.stroke()}
  const rails=items.filter(o=>o.kind==='rail');
  for(const r of rails){if(r.tram)continue;traceLine(g,r.pts);g.strokeStyle='#958e83';g.lineWidth=3.2;g.stroke()}
  const roads=items.filter(o=>o.kind==='road').sort((a,b)=>a.rank-b.rank);
  // sidewalks in built-up roads
  for(const r of roads){const t=r.tags;if(r.unp||!(/^(residential|living_street|tertiary|secondary|primary|unclassified)$/.test(t.highway))||t.sidewalk==='no'||t.sidewalk==='none')continue;
    if(!(t.sidewalk||t.highway==='residential'||t.highway==='living_street'))continue;
    traceLine(g,r.pts);g.strokeStyle='#bab5ab';g.lineWidth=r.w+3.6;g.stroke()}
  for(const r of roads){traceLine(g,r.pts);g.strokeStyle=r.unp?'#8f8062':'#3c3d41';g.lineWidth=r.w+.6;g.stroke()}
  for(const r of roads){traceLine(g,r.pts);g.strokeStyle=r.col;g.lineWidth=r.w;g.stroke();traceLine(m,r.pts);m.strokeStyle=r.unp?'#00ff00':'#ff0000';m.lineWidth=r.w+.4;m.stroke()}
  // markings
  const LW=Math.max(.16,.9/S);
  g.strokeStyle='rgba(240,238,230,.9)';g.lineWidth=LW;g.lineCap='butt';
  for(const r of roads){
    if(r.unp){traceLine(g,offsetLine(r.pts,.75));g.strokeStyle='rgba(70,58,38,.35)';g.lineWidth=.5;g.stroke();traceLine(g,offsetLine(r.pts,-.75));g.stroke();g.strokeStyle='rgba(240,238,230,.9)';g.lineWidth=LW;continue}
    const hw=r.tags.highway;if(r.w<4.5||hw==='service'||hw==='pedestrian'||hw==='living_street')continue;
    if(r.rank>=5){g.setLineDash([]);for(const s of [-1,1]){traceLine(g,offsetLine(r.pts,s*(r.w/2-.45)));g.stroke()}}
    const lanes=r.lanes||Math.max(r.oneway?1:2,Math.round(r.w/3.3));
    if(r.oneway){if(lanes>1){g.setLineDash([3,6]);const lw=r.w/lanes;for(let k=1;k<lanes;k++){traceLine(g,offsetLine(r.pts,-r.w/2+k*lw));g.stroke()}}}
    else{g.setLineDash(r.rank>=6?[6,6]:[3,6]);traceLine(g,r.pts);g.stroke();
      if(lanes>=4){const lw=r.w/lanes;for(let k=1;k<lanes/2;k++)for(const s of [-1,1]){traceLine(g,offsetLine(r.pts,s*k*lw));g.stroke()}}}
  }
  g.setLineDash([]);g.lineCap='round';
  for(const r of rails){const o=r.tram?.72:.72;for(const s of [-1,1]){traceLine(g,offsetLine(r.pts,s*o));g.strokeStyle=r.tram?'#77736d':'#5a5650';g.lineWidth=.16;g.stroke()}}
  // building footprints (contact shadow)
  g.fillStyle='rgba(60,58,54,.55)';
  for(const b of items)if(b.kind==='bld'){tracePoly(g,b.rings);g.fill('evenodd')}
  // surface mask
  const d=m.getImageData(0,0,CH,CH).data,surf=new Uint8Array(CH*CH);
  for(let i=0;i<CH*CH;i++){const R=d[i*4],G=d[i*4+1],B=d[i*4+2];surf[i]=R>110?2:G>110?1:B>110?3:0}
  c.surf=surf;
  const mini=document.createElement('canvas');mini.width=mini.height=256;mini.getContext('2d').drawImage(cv,0,0,256,256);c.mini=mini;
  const tex=new THREE.CanvasTexture(cv);tex.anisotropy=Math.min(8,renderer.capabilities.getMaxAnisotropy());
  return tex;
}

/* ---------------- buildings ---------------- */
const WALLS=['#efe8da','#e9dfca','#f3efe6','#ddd1b8','#e8d7c6','#d6dad2','#f0e2bd','#d9cfc0','#c9c3b8'].map(c=>new THREE.Color(c));
const ROOFS=['#9b3b2a','#a8472f','#7e3428','#5b4d49','#45464b','#8a4a36','#6d3326'].map(c=>new THREE.Color(c));
const FLAT=new THREE.Color('#8e8c87');
function colorTag(v){if(!v)return null;try{const c=new THREE.Color();c.setStyle(v.trim());return c}catch(e){return null}}
function bldHeight(t,size,r){
  let h=parseNum(t.height);
  const lv=parseNum(t['building:levels']),rl=parseNum(t['roof:levels'])||0;
  if(!(h>0)&&lv>0)h=lv*3.1+.6;
  if(!(h>0)){const ty=t.building;
    h={house:6.2,detached:6.5,semidetached_house:6.5,terrace:7.5,bungalow:3.8,garage:2.8,garages:2.8,shed:2.6,hut:2.8,cabin:3,apartments:12.5,dormitory:12,hotel:16,commercial:11,office:13,retail:6.5,supermarket:6,kiosk:3,industrial:8,warehouse:8,manufacture:9,church:15,chapel:7,cathedral:24,school:10,university:13,kindergarten:5,hospital:16,public:10,civic:10,train_station:9,farm:7,farm_auxiliary:6.5,barn:7,stable:5,greenhouse:3.5,service:3,transformer_tower:6,toilets:3,parking:9,static_caravan:3}[ty];
    if(!h)h=size<40?3:size<120?6.2:size<400?8:size<1500?11:13;
    h*=.9+r*.25;}
  return {h:clamp(h,2.4,300),rl};
}
function pitched(t,size,h){
  const s=t['roof:shape'];
  if(s)return /gabled|hipped|half-hipped|mansard|gambrel|saltbox|pyramidal/.test(s)?(s.includes('hip')||s==='pyramidal'?'hip':'gable'):null;
  if(size>650||h>16)return null;
  if(/^(industrial|warehouse|commercial|retail|supermarket|garage|garages|office|hospital|parking|manufacture|service|greenhouse)$/.test(t.building))return null;
  return hash(t.building.length*31+Math.round(size))<.12?'hip':'gable';
}
function obb(ring){
  let best=null;
  for(let i=0;i<ring.length-1;i++){const a=ring[i],b=ring[i+1];let ux=b[0]-a[0],uz=b[1]-a[1];const l=Math.hypot(ux,uz);if(l<.5)continue;ux/=l;uz/=l;
    let a0=1e9,a1=-1e9,b0=1e9,b1=-1e9;for(const p of ring){const s=p[0]*ux+p[1]*uz,t=-p[0]*uz+p[1]*ux;a0=Math.min(a0,s);a1=Math.max(a1,s);b0=Math.min(b0,t);b1=Math.max(b1,t)}
    const ar=(a1-a0)*(b1-b0);if(!best||ar<best.ar)best={ar,ux,uz,a0,a1,b0,b1}}
  if(!best)return null;
  let {ux,uz,a0,a1,b0,b1}=best;
  if(a1-a0<b1-b0){[ux,uz]=[-uz,ux];const na0=b0,na1=b1,nb0=-a1,nb1=-a0;a0=na0;a1=na1;b0=nb0;b1=nb1;}
  const ca=(a0+a1)/2,cb=(b0+b1)/2;
  return {ux,uz,cx:ca*ux-cb*uz,cz:ca*uz+cb*ux,L:(a1-a0)/2,Sh:(b1-b0)/2};
}
function buildBuildings(c,blds,cells){
  const P=[],Nn=[],U=[],C=[];
  const v3=new THREE.Vector3(),e1=new THREE.Vector3(),e2=new THREE.Vector3();
  const tri=(a,b,d,col,ua,ub,ud,ref)=>{
    e1.set(b[0]-a[0],b[1]-a[1],b[2]-a[2]);e2.set(d[0]-a[0],d[1]-a[1],d[2]-a[2]);v3.crossVectors(e1,e2);
    if(ref){const mx=(a[0]+b[0]+d[0])/3-ref[0],my=(a[1]+b[1]+d[1])/3-ref[1],mz=(a[2]+b[2]+d[2])/3-ref[2];if(v3.x*mx+v3.y*my+v3.z*mz<0){[b,d]=[d,b];[ub,ud]=[ud,ub];v3.negate()}}
    v3.normalize();P.push(...a,...b,...d);for(let k=0;k<3;k++){Nn.push(v3.x,v3.y,v3.z);C.push(col.r,col.g,col.b)}U.push(...ua,...ub,...ud);
  };
  const W0=[.01,.01];
  for(const b of blds){
    const t=b.tags,r=hash(Math.abs(b.id)),{h}=bldHeight(t,b.size,r);
    const outer=b.rings.outer;
    let gmin=1e9,gmax=-1e9;for(const ring of outer)for(const p of ring){const y=height(p[0],p[1]);gmin=Math.min(gmin,y);gmax=Math.max(gmax,y)}
    const minH=parseNum(t.min_height)||0;
    const y0=gmin-1.2+minH,base=gmax;
    const roofType=pitched(t,b.size,h);
    const ob=roofType&&outer.length===1?obb(outer[0]):null;
    const rh=ob?clamp(ob.Sh*2*.42,1.2,6.5):0;
    const wallTop=base+Math.max(2.4,ob?h-rh*.75:h);
    const wc=colorTag(t['building:colour'])||WALLS[Math.floor(r*WALLS.length)].clone().offsetHSL(0,0,(hash(b.id*7)-.5)*.06);
    const rc=colorTag(t['roof:colour'])||(ob?ROOFS[Math.floor(hash(b.id*13)*ROOFS.length)]:FLAT.clone().offsetHSL(0,0,(r-.5)*.08));
    // walls
    for(const ring0 of [...outer,...b.rings.inner]){
      let ring=ring0.slice();if(eqp(ring[0],ring[ring.length-1]))ring.pop();if(ring.length<3)continue;
      const isOuter=outer.includes(ring0);if((areaOf(ring)>0)!==isOuter)ring.reverse();
      let dist=hash(b.id)*16;
      for(let i=0;i<ring.length;i++){
        const p=ring[i],q=ring[(i+1)%ring.length],len=Math.hypot(q[0]-p[0],q[1]-p[1]);if(len<.05)continue;
        const u0=dist/16,u1=(dist+len)/16,v1=(wallTop-y0)/12.4;dist+=len;
        const A=[p[0],y0,p[1]],B=[q[0],y0,q[1]],Cc=[q[0],wallTop,q[1]],D=[p[0],wallTop,p[1]];
        const nx=(q[1]-p[1])/len,nz=-(q[0]-p[0])/len,ref=[(p[0]+q[0])/2-nx,y0,(p[1]+q[1])/2-nz];
        tri(A,B,Cc,wc,[u0,0],[u1,0],[u1,v1],ref);tri(A,Cc,D,wc,[u0,0],[u1,v1],[u0,v1],ref);
        addCol({x1:p[0],z1:p[1],x2:q[0],z2:q[1],top:wallTop+rh},c.key,cells);
      }
    }
    // roof
    if(ob){
      const o=.4,L=ob.L+o,Sh=ob.Sh+o,ux=ob.ux,uz=ob.uz,vx=-uz,vz=ux,ry=wallTop+rh,hipIn=roofType==='hip'?Math.min(ob.Sh,ob.L*.7):0;
      const pt=(a,s,y)=>[ob.cx+ux*a+vx*s,y,ob.cz+uz*a+vz*s];
      const E1=pt(-L,-Sh,wallTop-.15),E2=pt(L,-Sh,wallTop-.15),E3=pt(L,Sh,wallTop-.15),E4=pt(-L,Sh,wallTop-.15),R1=pt(-L+hipIn,0,ry),R2=pt(L-hipIn,0,ry);
      const ref=[ob.cx,wallTop-2,ob.cz];
      tri(E1,E2,R2,rc,W0,W0,W0,ref);tri(E1,R2,R1,rc,W0,W0,W0,ref);
      tri(E3,E4,R1,rc,W0,W0,W0,ref);tri(E3,R1,R2,rc,W0,W0,W0,ref);
      const gc=roofType==='hip'?rc:wc;
      tri(E4,E1,R1,gc,W0,W0,W0,ref);tri(E2,E3,R2,gc,W0,W0,W0,ref);
      // ceiling cap so gaps never show sky
      const cap=wallTop-.2;
      tri(pt(-ob.L,-ob.Sh,cap),pt(ob.L,-ob.Sh,cap),pt(ob.L,ob.Sh,cap),rc,W0,W0,W0,[ob.cx,cap-5,ob.cz]);
      tri(pt(-ob.L,-ob.Sh,cap),pt(ob.L,ob.Sh,cap),pt(-ob.L,ob.Sh,cap),rc,W0,W0,W0,[ob.cx,cap-5,ob.cz]);
    }else{
      for(const ring0 of outer){
        let ring=ring0.slice();if(eqp(ring[0],ring[ring.length-1]))ring.pop();if(ring.length<3)continue;
        const holes=b.rings.inner.filter(hr=>inter(bbOf(hr),bbOf(ring))).map(hr=>{const x=hr.slice();if(eqp(x[0],x[x.length-1]))x.pop();return x.map(p=>new THREE.Vector2(p[0],p[1]))});
        const contour=ring.map(p=>new THREE.Vector2(p[0],p[1]));
        let idx;try{idx=THREE.ShapeUtils.triangulateShape(contour,holes)}catch(e){continue}
        const all=contour.concat(...holes),y=wallTop;
        for(const [i,j,k] of idx){const a=all[i],bb=all[j],d=all[k];tri([a.x,y,a.y],[bb.x,y,bb.y],[d.x,y,d.y],rc,W0,W0,W0,[a.x,y-10,a.y])}
      }
    }
  }
  if(!P.length)return null;
  const g=new THREE.BufferGeometry();
  g.setAttribute('position',new THREE.Float32BufferAttribute(P,3));g.setAttribute('normal',new THREE.Float32BufferAttribute(Nn,3));
  g.setAttribute('uv',new THREE.Float32BufferAttribute(U,2));g.setAttribute('color',new THREE.Float32BufferAttribute(C,3));
  const mesh=new THREE.Mesh(g,MAT.bld);mesh.castShadow=true;mesh.receiveShadow=true;return mesh;
}

/* ---------------- trees ---------------- */
function pip(x,z,rings){let ins=false;for(const r of [...rings.outer,...rings.inner]){for(let i=0,j=r.length-1;i<r.length;j=i++){const a=r[i],b=r[j];if(((a[1]>z)!==(b[1]>z))&&(x<(b[0]-a[0])*(z-a[1])/(b[1]-a[1])+a[0]))ins=!ins}}return ins}
function buildTrees(c,items,cells){
  const R=rng(Math.imul(c.i,73856093)^Math.imul(c.j,19349663)),list=[];
  const free=(x,z)=>{const s=surfaceAt(x,z);return s===0};
  for(const t of treeNodes.values()){if(t.x>=c.x0&&t.x<c.x0+CH&&t.z>=c.z0&&t.z<c.z0+CH&&free(t.x,t.z))list.push({x:t.x,z:t.z,s:.8+R()*.5,con:t.t.leaf_type==='needleleaved'})}
  for(const w of items){
    if(w.kind==='trow'){for(let k=0;k<w.pts.length-1;k++){const a=w.pts[k],b=w.pts[k+1],l=Math.hypot(b[0]-a[0],b[1]-a[1]);for(let s=0;s<l;s+=9){const x=lerp(a[0],b[0],s/l),z=lerp(a[1],b[1],s/l);if(x>=c.x0&&x<c.x0+CH&&z>=c.z0&&z<c.z0+CH&&free(x,z))list.push({x,z,s:.8+R()*.4,con:false})}}}
    if(w.kind!=='area')continue;
    const st=w.st,dens=st.forest?7:(st.c==='#86b45a'||st.c==='#8bb763')?17:st.c==='#a9b488'?26:0;
    if(!dens)continue;
    const x0=Math.max(c.x0,w.bb[0]),x1=Math.min(c.x0+CH,w.bb[2]),z0=Math.max(c.z0,w.bb[1]),z1=Math.min(c.z0+CH,w.bb[3]);
    for(let x=Math.ceil(x0/dens)*dens;x<x1;x+=dens)for(let z=Math.ceil(z0/dens)*dens;z<z1;z+=dens){
      if(!st.forest&&R()<.45)continue;
      const px=x+(R()-.5)*dens*.9,pz=z+(R()-.5)*dens*.9;
      if(!pip(px,pz,w.rings)||!free(px,pz))continue;
      if(!st.forest&&nearBuilding(px,pz,items))continue;
      list.push({x:px,z:pz,s:.75+R()*.6,con:st.forest?(st.needle?R()<.9:R()<.45):R()<.2});
      if(list.length>3500)break;
    }
  }
  if(!list.length)return null;
  const nCon=list.filter(t=>t.con).length,nBr=list.length-nCon;
  const trunks=new THREE.InstancedMesh(MAT.trunkG,MAT.trunk,list.length);
  const cons=new THREE.InstancedMesh(MAT.conG,MAT.con,Math.max(1,nCon));cons.count=nCon;
  const brs=new THREE.InstancedMesh(MAT.broadG,MAT.broad,Math.max(1,nBr));brs.count=nBr;
  const M=new THREE.Matrix4(),Q=new THREE.Quaternion(),Sv=new THREE.Vector3(),Pv=new THREE.Vector3(),col=new THREE.Color(),Y=new THREE.Vector3(0,1,0);
  let ic=0,ib=0;
  list.forEach((t,i)=>{
    const y=height(t.x,t.z)-.15;
    if(t.con){M.compose(Pv.set(t.x,y,t.z),Q.identity(),Sv.set(t.s,3*t.s,t.s));trunks.setMatrixAt(i,M);
      M.compose(Pv.set(t.x,y+2*t.s,t.z),Q.identity(),Sv.set(t.s,(9+R()*6)*t.s,t.s));cons.setMatrixAt(ic,M);cons.setColorAt(ic,col.set('#2f4a2a').offsetHSL((R()-.5)*.03,0,(R()-.5)*.07));ic++}
    else{M.compose(Pv.set(t.x,y,t.z),Q.identity(),Sv.set(t.s*1.2,4*t.s,t.s*1.2));trunks.setMatrixAt(i,M);
      Q.setFromAxisAngle(Y,R()*6);M.compose(Pv.set(t.x,y+5.2*t.s,t.z),Q,Sv.set(3.3*t.s,2.9*t.s,3.3*t.s));brs.setMatrixAt(ib,M);brs.setColorAt(ib,col.set('#4f6f30').offsetHSL((R()-.5)*.05,(R()-.5)*.1,(R()-.5)*.09));ib++}
    addCol({t:1,x:t.x,z:t.z,r:.4*t.s},c.key,cells);
  });
  const grp=new THREE.Group();
  for(const m of [trunks,cons,brs]){if(!m.count){m.dispose&&m.dispose();continue}m.castShadow=true;m.frustumCulled=false;m.userData.sharedGeo=true;grp.add(m)}
  return grp;
}
function nearBuilding(x,z,items){for(const b of items)if(b.kind==='bld'&&x>b.bb[0]-3&&x<b.bb[2]+3&&z>b.bb[1]-3&&z<b.bb[3]+3)return true;return false}

/* ---------------- chunk lifecycle ---------------- */
function getChunk(i,j){const k=i+','+j;let c=chunks.get(k);if(!c){c={i,j,key:k,x0:i*CH-CH/2,z0:j*CH-CH/2,data:false,fetching:false,fails:0,retry:0,built:false,building:false,group:null,cells:new Set(),blds:[]};chunks.set(k,c)}return c}
function buildChunk(c){
  const my=gen;
  const bb=[c.x0-30,c.z0-30,c.x0+CH+30,c.z0+CH+30];
  const items=[];for(const w of ways.values())if(inter(w.bb,bb))items.push(w);for(const r of rels.values())if(inter(r.bb,bb))items.push(r);
  if(!c.h)computeHeights(c);
  const tex=drawGround(c,items);
  const grp=new THREE.Group();
  const geo=new THREE.PlaneGeometry(CH,CH,HN-1,HN-1);geo.rotateX(-Math.PI/2);
  const pos=geo.attributes.position;
  for(let k=0;k<pos.count;k++){const lx=pos.getX(k)+CH/2,lz=pos.getZ(k)+CH/2,i=Math.round(lx/HG),j=Math.round(lz/HG);pos.setY(k,c.h[j*HN+i])}
  geo.computeVertexNormals();
  const ground=new THREE.Mesh(geo,new THREE.MeshLambertMaterial({map:tex}));ground.position.set(c.x0+CH/2,0,c.z0+CH/2);ground.receiveShadow=true;grp.add(ground);
  const blds=items.filter(o=>o.kind==='bld'&&o.cx>=c.x0&&o.cx<c.x0+CH&&o.cz>=c.z0&&o.cz<c.z0+CH&&!o.built);
  blds.forEach(b=>b.built=true);c.blds=blds;
  const bm=buildBuildings(c,blds,c.cells);if(bm)grp.add(bm);
  const tg=buildTrees(c,items,c.cells);if(tg)grp.add(tg);
  if(my!==gen){dispose(grp);return}
  root.add(grp);c.group=grp;c.built=true;c.tex=tex;
}
function dispose(grp){grp.traverse(o=>{if(o.geometry&&!o.userData.sharedGeo&&!o.isInstancedMesh)o.geometry.dispose();if(o.isInstancedMesh)o.dispose&&o.dispose();if(o.material&&o.material!==MAT.bld&&o.material!==MAT.trunk&&o.material!==MAT.con&&o.material!==MAT.broad){if(o.material.map)o.material.map.dispose();o.material.dispose()}})}
function dropChunk(c){
  if(c.group){root.remove(c.group);dispose(c.group);c.group=null}
  for(const k of c.cells){const a=colGrid.get(k);if(a){const f=a.filter(x=>x.ck!==c.key);if(f.length)colGrid.set(k,f);else colGrid.delete(k)}}
  c.cells.clear();c.blds.forEach(b=>b.built=false);c.blds=[];c.built=false;c.surf=null;c.mini=null;
}

async function fetchRegion(list){
  const my=gen;
  list.forEach(c=>c.fetching=true);fetching++;W.busy=fetching;
  const pad=60,x0=Math.min(...list.map(c=>c.x0))-pad,z0=Math.min(...list.map(c=>c.z0))-pad,x1=Math.max(...list.map(c=>c.x0+CH))+pad,z1=Math.max(...list.map(c=>c.z0+CH))+pad;
  try{
    const [els]=await Promise.all([fetchOSM(x0,z0,x1,z1,abort.signal),ensureElev(x0-20,z0-20,x1+20,z1+20)]);
    if(my!==gen)return;
    ingest(els);
    for(const c of list){c.data=true;c.fails=0;computeHeights(c)}
    W.error=null;
  }catch(e){
    if(my!==gen)return;
    for(const c of list){c.fails++;c.retry=performance.now()+Math.min(30000,2500*2**c.fails)}
    W.error=e.message||'Kartendaten nicht erreichbar';
    throw e;
  }finally{
    if(my===gen){list.forEach(c=>c.fetching=false);fetching--;W.busy=fetching}
  }
}

/* ---------------- public API ---------------- */
export async function loadArea(onStep){
  initShared();
  unloadAll();
  gen++;abort=new AbortController();
  root=new THREE.Group();scene.add(root);root.add(MAT.base);
  onStep('Lade Höhendaten',.1);
  await ensureElev(-CH*1.6,-CH*1.6,CH*1.6,CH*1.6);
  const h0=demLocal(0,0);W.h0=h0==null?0:h0;MAT.base.position.y=-3;
  onStep('Lade Straßen und Gebäude',.25);
  const init=[];for(let j=-1;j<=1;j++)for(let i=-1;i<=1;i++)init.push(getChunk(i,j));
  await fetchRegion(init);
  const order=init.slice().sort((a,b)=>(Math.abs(a.i)+Math.abs(a.j))-(Math.abs(b.i)+Math.abs(b.j)));
  for(let k=0;k<order.length;k++){onStep('Baue Welt',.45+.5*k/order.length);await new Promise(r=>setTimeout(r,0));buildChunk(order[k])}
  let ymin=1e9;for(const c of init)for(const v of c.h)ymin=Math.min(ymin,v);MAT.base.position.y=ymin-2;
  W.ready=true;onStep('Fertig',1);
}
export function unloadAll(){
  gen++;if(abort)abort.abort();
  for(const c of chunks.values())dropChunk(c);
  if(root){root.remove(MAT&&MAT.base);scene.remove(root);root=null}
  ways=new Map();rels=new Map();treeNodes=new Map();chunks=new Map();roadGrid=new Map();colGrid=new Map();
  fetching=0;W.busy=0;W.ready=false;W.error=null;
}
let tick=0;
export function updateWorld(x,z,dt){
  if(!W.ready)return;
  tick-=dt;if(tick>0)return;tick=.25;
  const ci=Math.round(x/CH),cj=Math.round(z/CH),now=performance.now();
  // build nearby
  let built=0;
  for(let r=0;r<=BUILD_R&&!built;r++)for(let j=cj-r;j<=cj+r&&!built;j++)for(let i=ci-r;i<=ci+r&&!built;i++){
    if(Math.max(Math.abs(i-ci),Math.abs(j-cj))!==r)continue;const c=getChunk(i,j);
    if(c.data&&!c.built){buildChunk(c);built=1}
  }
  // fetch ahead (one request at a time)
  if(fetching===0){
    let best=null,bd=1e9;
    for(let j=cj-FETCH_R;j<=cj+FETCH_R;j++)for(let i=ci-FETCH_R;i<=ci+FETCH_R;i++){const c=getChunk(i,j);if(c.data||c.fetching||now<c.retry)continue;const d=Math.hypot(i-ci,j-cj);if(d<bd){bd=d;best=c}}
    if(best){const row=[best];fetchRegion(row).catch(()=>{})}
  }
  // drop far away
  for(const c of chunks.values())if(c.built&&Math.max(Math.abs(c.i-ci),Math.abs(c.j-cj))>DROP_R)dropChunk(c);
  let wait=false;for(let j=cj-1;j<=cj+1;j++)for(let i=ci-1;i<=ci+1;i++){const c=chunks.get(i+','+j);if(!c||!c.built)wait=true}
  W.status=wait?'Lade Umgebung …':'';
}
export function builtChunks(){const a=[];for(const c of chunks.values())if(c.built&&c.mini)a.push(c);return a}
export function spawnPoint(){
  const car=w=>!/^(track|service|pedestrian|raceway)$/.test(w.tags.highway)&&w.tags.access!=='no';
  const r=nearestRoad(0,0,450,car)||nearestRoad(0,0,450);
  if(r)return {x:r.x,z:r.z,th:Math.atan2(r.dx,r.dz),name:r.w.tags.name||null};
  return {x:0,z:0,th:0,name:null};
}
