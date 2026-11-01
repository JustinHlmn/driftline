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
  facadeTextures();
  MAT.detail=detailTex();
  MAT.water=new THREE.MeshPhongMaterial({color:'#386a87',specular:'#d6e6f0',shininess:140,transparent:true,opacity:.9});
  MAT.lamp=new THREE.MeshLambertMaterial({color:'#3b3e42'});MAT.lampG=lampGeo();
  for(const k of ['trunk','con','broad','water','lamp'])MAT[k].userData.shared=true;
  MAT.base=new THREE.Mesh(new THREE.PlaneGeometry(9000,9000),groundMat(new THREE.MeshLambertMaterial({color:'#93a96a'})));
  MAT.base.rotation.x=-Math.PI/2;MAT.base.receiveShadow=true;
}

function detailTex(){
  const N=256,c=document.createElement('canvas');c.width=c.height=N;const g=c.getContext('2d'),d=g.createImageData(N,N);
  const hh=(i,j,p)=>{i=((i%p)+p)%p;j=((j%p)+p)%p;let n=Math.imul(i,374761393)+Math.imul(j,668265263)+p*97|0;n=Math.imul(n^(n>>>13),1274126177);return ((n^(n>>>16))>>>0)/4294967296};
  const vn=(x,y,p)=>{const i=Math.floor(x),j=Math.floor(y),fx=x-i,fy=y-j,ux=fx*fx*(3-2*fx),uy=fy*fy*(3-2*fy);const a=hh(i,j,p),b=hh(i+1,j,p),cc=hh(i,j+1,p),e=hh(i+1,j+1,p);return a+(b-a)*ux+(cc-a)*uy+(a-b-cc+e)*ux*uy};
  for(let y=0;y<N;y++)for(let x=0;x<N;x++){const k=(y*N+x)*4;
    const r=(vn(x/16,y/16,16)*.5+vn(x/8,y/8,32)*.3+vn(x/4,y/4,64)*.2);
    const gg=Math.random()*.6+vn(x/2,y/2,128)*.4;
    const b=vn(x/64,y/64,4)*.7+vn(x/32,y/32,8)*.3;
    d.data[k]=r*255;d.data[k+1]=gg*255;d.data[k+2]=b*255;d.data[k+3]=255}
  g.putImageData(d,0,0);const t=new THREE.CanvasTexture(c);t.wrapS=t.wrapT=THREE.RepeatWrapping;t.anisotropy=Math.min(8,renderer.capabilities.getMaxAnisotropy());return t;
}
function groundMat(m){
  m.onBeforeCompile=sh=>{
    sh.uniforms.dTex={value:MAT.detail};
    sh.vertexShader=sh.vertexShader.replace('#include <common>','#include <common>\nvarying vec2 vDW;').replace('#include <begin_vertex>','#include <begin_vertex>\nvDW=(modelMatrix*vec4(position,1.0)).xz;');
    sh.fragmentShader=sh.fragmentShader.replace('#include <common>','#include <common>\nuniform sampler2D dTex;varying vec2 vDW;').replace('#include <map_fragment>',
      '#include <map_fragment>\nfloat dA=texture2D(dTex,vDW*0.22).r,dB=texture2D(dTex,vDW*1.3+0.37).g,dC=texture2D(dTex,vDW*0.012).b;\ndiffuseColor.rgb*=(0.8+0.4*dA)*(0.9+0.2*dB)*(0.84+0.32*dC);');
  };
  m.customProgramCacheKey=()=>'dlground';
  return m;
}
function lampGeo(){
  const parts=[];
  const pole=new THREE.CylinderGeometry(.06,.09,6.2,6);pole.translate(0,3.1,0);parts.push(pole);
  const arm=new THREE.BoxGeometry(1.4,.08,.08);arm.translate(.7,6.1,0);parts.push(arm);
  const head=new THREE.BoxGeometry(.6,.14,.28);head.translate(1.35,6.02,0);parts.push(head);
  const P=[],N=[];for(const g0 of parts){const g=g0.toNonIndexed();P.push(...g.attributes.position.array);N.push(...g.attributes.normal.array)}
  const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(P,3));g.setAttribute('normal',new THREE.Float32BufferAttribute(N,3));return g;
}
const isSidewalkRoad=r=>{const t=r.tags;if(r.unp||!(/^(residential|living_street|tertiary|secondary|primary|unclassified)$/.test(t.highway))||t.sidewalk==='no'||t.sidewalk==='none')return false;return !!(t.sidewalk||t.highway==='residential'||t.highway==='living_street')};

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
  for(const r of roads){if(!isSidewalkRoad(r))continue;traceLine(g,r.pts);g.strokeStyle='#bdb8ae';g.lineWidth=r.w+3.6;g.stroke()}
  for(const r of roads){if(!isSidewalkRoad(r))continue;traceLine(g,r.pts);g.strokeStyle='#dcd8cf';g.lineWidth=r.w+1.0;g.stroke()}
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
const FLOOR=3.1,BAY=3.0,PLINTH=.45;
const WALLS=['#f2ece0','#ece2cf','#f6f2ea','#e3d6bd','#ecdccb','#dde1d9','#f2e6c6','#e0d6c7','#d4cdc2','#efe0d0','#e5e9ec'].map(c=>new THREE.Color(c));
const ROOFS=['#a8412c','#b44e33','#8a3a2b','#5d4f4b','#4a4b50','#93503a','#753628','#9c5a3c'].map(c=>new THREE.Color(c));
const FLAT=new THREE.Color('#9a9892');
function colorTag(v){if(!v)return null;try{const c=new THREE.Color();c.setStyle(v.trim());return c}catch(e){return null}}
function bldHeight(t,size,r){
  let h=parseNum(t.height);
  const lv=parseNum(t['building:levels']);
  if(!(h>0)&&lv>0)h=lv*FLOOR+PLINTH+(parseNum(t['roof:levels'])>0?2.5:0);
  if(!(h>0)){const ty=t.building;
    h={house:6.5,detached:6.8,semidetached_house:6.8,terrace:7.5,bungalow:3.9,garage:2.9,garages:2.9,shed:2.7,hut:2.9,cabin:3.2,apartments:12.8,dormitory:12.5,hotel:16,commercial:10,office:13,retail:6.6,supermarket:6.5,kiosk:3.2,industrial:8,warehouse:8,manufacture:9,church:15,chapel:7,cathedral:24,school:10,university:13,kindergarten:5,hospital:16,public:10,civic:10,train_station:9,farm:7,farm_auxiliary:6.5,barn:7,stable:5,greenhouse:3.5,service:3.2,transformer_tower:6,toilets:3.2,parking:9,static_caravan:3}[ty];
    if(!h)h=size<40?3.2:size<140?6.5:size<400?9.8:size<1500?12.9:16;
    h*=.95+r*.15;}
  return clamp(h,2.6,300);
}
function roofKind(t,size,h,st){
  const s=t['roof:shape'];
  if(s)return /gabled|half-hipped|mansard|gambrel|saltbox/.test(s)?'gable':/hipped|pyramidal/.test(s)?'hip':null;
  if(st==='glass'||size>700||h>17)return null;
  if(/^(industrial|warehouse|commercial|retail|supermarket|garages|office|hospital|parking|manufacture|service|greenhouse|kiosk)$/.test(t.building))return null;
  if(t.building==='garage'&&size<40)return null;
  return hash(Math.round(size*7))<.15?'hip':'gable';
}
function facadeStyle(t,h,r){
  const b=t.building||'',m=t['building:material']||t['building:facade:material']||'';
  if(/^(church|chapel|cathedral|mosque|synagogue|temple|shrine)$/.test(b)||t.amenity==='place_of_worship')return 'stone';
  if(/^(industrial|warehouse|manufacture|service|hangar|barn|farm_auxiliary|garage|garages|shed|storage_tank|stable|greenhouse|transformer_tower|carport|hut)$/.test(b))return 'ind';
  if(/brick/.test(m))return 'brick';
  if(/glass/.test(m)||(h>22&&/^(office|commercial|yes|hotel|university|hospital)$/.test(b)))return 'glass';
  if(h>10.5||/^(apartments|residential|dormitory|hotel|office|commercial|school|university|public|civic|hospital|retail|kindergarten|supermarket|train_station)$/.test(b))return r<.2?'brick':'apart';
  return r<.1?'brick':r<.42?'house2':'house';
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
  return {ux,uz,cx:ca*ux-cb*uz,cz:ca*uz+cb*ux,L:(a1-a0)/2,Sh:(b1-b0)/2,fill:best.ar};
}
/* geometry buckets per material */
function GB(){return {P:[],N:[],U:[],C:[]}}
const _e1=new THREE.Vector3(),_e2=new THREE.Vector3(),_n=new THREE.Vector3();
function tri(G,a,b,d,ua,ub,ud,col,ref,nExp){
  _e1.set(b[0]-a[0],b[1]-a[1],b[2]-a[2]);_e2.set(d[0]-a[0],d[1]-a[1],d[2]-a[2]);_n.crossVectors(_e1,_e2);
  if(_n.lengthSq()<1e-10)return;
  let flip=false;
  if(nExp)flip=_n.x*nExp[0]+_n.y*nExp[1]+_n.z*nExp[2]<0;
  else if(ref){const mx=(a[0]+b[0]+d[0])/3-ref[0],my=(a[1]+b[1]+d[1])/3-ref[1],mz=(a[2]+b[2]+d[2])/3-ref[2];flip=_n.x*mx+_n.y*my+_n.z*mz<0}
  if(flip){[b,d]=[d,b];[ub,ud]=[ud,ub];_n.negate()}
  if(nExp)_n.set(nExp[0],nExp[1],nExp[2]);
  _n.normalize();
  G.P.push(a[0],a[1],a[2],b[0],b[1],b[2],d[0],d[1],d[2]);
  for(let k=0;k<3;k++){G.N.push(_n.x,_n.y,_n.z);G.C.push(col.r,col.g,col.b)}
  G.U.push(ua[0],ua[1],ub[0],ub[1],ud[0],ud[1]);
}
function quad(G,a,b,c,d,ua,ub,uc,ud,col,n){tri(G,a,b,c,ua,ub,uc,col,null,n);tri(G,a,c,d,ua,uc,ud,col,null,n)}
// vertical wall strip from p to q (outward normal n) between y0..y1, uv u0..u1 / v0..v1
function wall(G,p,q,y0,y1,u0,u1,v0,v1,col,n){quad(G,[p[0],y0,p[1]],[q[0],y0,q[1]],[q[0],y1,q[1]],[p[0],y1,p[1]],[u0,v0],[u1,v0],[u1,v1],[u0,v1],col,[n[0],0,n[1]])}
// oriented box (centre cx,cz; axis ux,uz), no bottom
function box(G,cx,y0,cz,w,h,d,ux,uz,col,us){
  const vx=-uz,vz=ux,hw=w/2,hd=d/2,y1=y0+h;
  const P=(a,s)=>[cx+ux*a+vx*s,cz+uz*a+vz*s];
  const c=[P(-hw,-hd),P(hw,-hd),P(hw,hd),P(-hw,hd)];
  const ns=[[-vx,-vz],[ux,uz],[vx,vz],[-ux,-uz]];
  for(let i=0;i<4;i++){const p=c[i],q=c[(i+1)%4],l=i%2?d:w;wall(G,p,q,y0,y1,0,l/us,0,h/us,col,ns[i])}
  quad(G,[c[0][0],y1,c[0][1]],[c[1][0],y1,c[1][1]],[c[2][0],y1,c[2][1]],[c[3][0],y1,c[3][1]],[0,0],[w/us,0],[w/us,d/us],[0,d/us],col,[0,1,0]);
}
const PLAIN=[.015,.015];
function buildBuildings(c,blds,cells){
  const B={};const g=k=>B[k]||(B[k]=GB());
  const white=new THREE.Color(1,1,1);
  for(const b of blds){
    const t=b.tags,r=hash(Math.abs(b.id)),r2=hash(Math.abs(b.id)*7+3),r3=hash(Math.abs(b.id)*13+5);
    const h=bldHeight(t,b.size,r);
    const st=facadeStyle(t,h,r2);
    const outer=b.rings.outer;
    let gmin=1e9,gmax=-1e9;for(const ring of outer)for(let i=0;i<ring.length;i+=Math.max(1,ring.length>>4)){const p=ring[i],y=height(p[0],p[1]);gmin=Math.min(gmin,y);gmax=Math.max(gmax,y)}
    const minH=parseNum(t.min_height)||0;
    const y0=gmin-1.2+minH,pt=gmax+PLINTH+minH;
    const rk=outer.length===1&&b.size<2500?roofKind(t,b.size,h,st):null;
    const ob=rk?obb(outer[0]):null;
    const roofOk=ob&&ob.fill<b.size*1.6;
    const rh=roofOk?clamp(ob.Sh*2*.45,1.4,7):0;
    const floors=Math.max(1,Math.round((h-PLINTH-(roofOk?rh*.55:0))/FLOOR));
    const wallTop=pt+floors*FLOOR;
    const shop=st!=='ind'&&st!=='stone'&&st!=='glass'&&floors>=2&&(t.shop||/^(retail|commercial|supermarket|kiosk)$/.test(t.building)||((st==='apart'||st==='brick')&&floors>=3&&r3>.55));
    let wc=colorTag(t['building:colour']);
    if(!wc)wc=(st==='brick'||st==='stone')?white.clone().offsetHSL(0,0,-r3*.08):st==='ind'?new THREE.Color(['#c9ced3','#b8c1c7','#d3cfc4','#9fb0bb','#c4c8c2'][Math.floor(r3*5)]):st==='glass'?new THREE.Color(['#cfe0ea','#d9e2e6','#c4d4dc'][Math.floor(r3*3)]):WALLS[Math.floor(r*WALLS.length)];
    const plc=wc.clone().multiplyScalar(.72);
    const rc=colorTag(t['roof:colour'])||(roofOk?ROOFS[Math.floor(r3*ROOFS.length)]:FLAT.clone().offsetHSL(0,0,(r-.5)*.06));
    // walls
    let doorSeg=null,doorScore=1e9,longSeg=null,longLen=0;
    for(const ring0 of [...outer,...b.rings.inner]){
      let ring=ring0.slice();if(eqp(ring[0],ring[ring.length-1]))ring.pop();if(ring.length<3)continue;
      const isOuter=outer.includes(ring0);if((areaOf(ring)>0)!==isOuter)ring.reverse();
      for(let i=0;i<ring.length;i++){
        const p=ring[i],q=ring[(i+1)%ring.length],len=Math.hypot(q[0]-p[0],q[1]-p[1]);if(len<.05)continue;
        const n=[(q[1]-p[1])/len,-(q[0]-p[0])/len];
        const bays=len<1.7?0:Math.max(1,Math.round(len/BAY));
        const u1=bays||0;
        wall(g('plinth'),p,q,y0,pt,0,len/2,0,(pt-y0)/2,plc,n);
        if(bays===0){wall(g(st),p,q,pt,wallTop,PLAIN[0],PLAIN[0],PLAIN[1],PLAIN[1],wc,n)}
        else if(shop){wall(g('shop'),p,q,pt,pt+FLOOR,0,u1,0,1,wc,n);wall(g(st),p,q,pt+FLOOR,wallTop,0,u1,1,floors,wc,n)}
        else wall(g(st),p,q,pt,wallTop,0,u1,0,floors,wc,n);
        addCol({x1:p[0],z1:p[1],x2:q[0],z2:q[1],top:wallTop+rh},c.key,cells);
        if(isOuter&&len>=3.2){
          if(len>longLen){longLen=len;longSeg={p,q,n,len,bays}}
          const mx=(p[0]+q[0])/2+n[0]*4,mz=(p[1]+q[1])/2+n[1]*4,nr=nearestRoad(mx,mz,45);
          const sc=(nr?nr.d:60)-len*.15;if(sc<doorScore){doorScore=sc;doorSeg={p,q,n,len,bays}}
        }
      }
    }
    // door (houses / apartments without shopfront)
    if(doorSeg&&!shop&&st!=='ind'&&st!=='glass'){
      const {p,q,n,len,bays}=doorSeg,k=bays>1?(Math.floor(bays/2)+.5)/bays:.5;
      const cx=lerp(p[0],q[0],k)+n[0]*.04,cz=lerp(p[1],q[1],k)+n[1]*.04,dx=(q[0]-p[0])/len,dz=(q[1]-p[1])/len,dw=st==='stone'?1.0:.62;
      const a=[cx-dx*dw,cz-dz*dw],bq=[cx+dx*dw,cz+dz*dw];
      wall(g('door'),a,bq,pt-.05,pt+(st==='stone'?3.4:2.45),0,1,0,1,white,n);
      // small steps
      box(g('plinth'),cx+n[0]*.45,pt-.6,cz+n[1]*.45,dw*2+.4,.6,.9,dx,dz,plc,1);
    }
    // balconies on the longest facade
    if((st==='apart'||st==='brick')&&floors>=3&&longSeg&&longSeg.bays>=3&&r3<.7&&longSeg!==doorSeg){
      const {p,q,n,len,bays}=longSeg,dx=(q[0]-p[0])/len,dz=(q[1]-p[1])/len,bw=len/bays;let cnt=0;
      for(let f=1;f<floors&&cnt<36;f++)for(let k=(f%2);k<bays&&cnt<36;k+=2){
        const s=(k+.5)*bw,cx=p[0]+dx*s+n[0]*.6,cz=p[1]+dz*s+n[1]*.6,y=pt+f*FLOOR-.12;
        box(g('plinth'),cx,y,cz,bw*.78,.16,1.2,dx,dz,plc,1);
        const ox=cx+n[0]*.58,oz=cz+n[1]*.58,hw=bw*.39;
        wall(g('rail'),[ox-dx*hw,oz-dz*hw],[ox+dx*hw,oz+dz*hw],y+.16,y+1.1,0,bw*.78/1.2,0,1,white,n);
        for(const sd of [-1,1]){const ex=cx+dx*hw*sd,ez=cz+dz*hw*sd,ns=[dx*sd,dz*sd];wall(g('rail'),[ex-n[0]*.6,ez-n[1]*.6],[ex+n[0]*.58,ez+n[1]*.58],y+.16,y+1.1,0,1,0,1,white,ns)}
        cnt++;
      }
    }
    // roof
    if(roofOk){
      const o=.45,L=ob.L+o,Sh=ob.Sh+o,ux=ob.ux,uz=ob.uz,vx=-uz,vz=ux,ry=wallTop+rh,hipIn=rk==='hip'?Math.min(ob.Sh,ob.L*.75):0,ey=wallTop-o*rh/ob.Sh;
      const pt3=(a,s,y)=>[ob.cx+ux*a+vx*s,y,ob.cz+uz*a+vz*s];
      const E1=pt3(-L,-Sh,ey),E2=pt3(L,-Sh,ey),E3=pt3(L,Sh,ey),E4=pt3(-L,Sh,ey),R1=pt3(-L+hipIn,0,ry),R2=pt3(L-hipIn,0,ry);
      const ref=[ob.cx,wallTop-3,ob.cz],slope=Math.hypot(Sh,ry-ey)/2,G=g('roof');
      tri(G,E1,E2,R2,[-L/2,0],[L/2,0],[(L-hipIn)/2,slope],rc,ref);tri(G,E1,R2,R1,[-L/2,0],[(L-hipIn)/2,slope],[(-L+hipIn)/2,slope],rc,ref);
      tri(G,E3,E4,R1,[L/2,0],[-L/2,0],[(-L+hipIn)/2,slope],rc,ref);tri(G,E3,R1,R2,[L/2,0],[(-L+hipIn)/2,slope],[(L-hipIn)/2,slope],rc,ref);
      if(rk==='hip'){tri(G,E4,E1,R1,[-Sh/2,0],[Sh/2,0],[0,slope],rc,ref);tri(G,E2,E3,R2,[-Sh/2,0],[Sh/2,0],[0,slope],rc,ref)}
      else{
        // gable walls (with an attic window when wide enough)
        const GW=g(st),gU=s=>.5+s/BAY,gV=y=>floors+(y-wallTop)/FLOOR,att=ob.Sh*2>6.5;
        for(const a of [-ob.L,ob.L]){const A=pt3(a,-ob.Sh,wallTop),Bq=pt3(a,ob.Sh,wallTop),T=pt3(a,0,ry-(o*rh/ob.Sh)*0);
          const nn=[ux*Math.sign(a),0,uz*Math.sign(a)];
          if(att)tri(GW,A,Bq,T,[gU(-ob.Sh),gV(wallTop)],[gU(ob.Sh),gV(wallTop)],[gU(0),gV(ry)],wc,null,nn);
          else tri(GW,A,Bq,T,PLAIN,PLAIN,PLAIN,wc,null,nn);}
        // gable edge boards
        const fasc=g('plinth');
        for(const a of [-L,L])for(const sd of [-1,1]){const A=pt3(a,sd*Sh,ey),T=pt3(a,0,ry),nn=[ux*Math.sign(a),0,uz*Math.sign(a)];
          const A2=[A[0],A[1]-.22,A[2]],T2=[T[0],T[1]-.22,T[2]];quad(fasc,A2,A,T,T2,[0,0],[1,0],[1,1],[0,1],rc.clone().multiplyScalar(.6),nn)}
      }
      // ceiling under the eaves so the roof never looks hollow
      const cy=wallTop-.02,cr=[ob.cx,cy+5,ob.cz];
      tri(g('plinth'),pt3(-L,-Sh,ey),pt3(L,-Sh,ey),pt3(L,Sh,ey),[0,0],[0,0],[0,0],plc,null,[0,-1,0]);
      tri(g('plinth'),pt3(-L,-Sh,ey),pt3(L,Sh,ey),pt3(-L,Sh,ey),[0,0],[0,0],[0,0],plc,null,[0,-1,0]);
      // chimney
      if(r<.65&&ob.L>3){const a=(r2-.5)*ob.L*1.1,s=(r3<.5?-1:1)*ob.Sh*.42,yb=ry-Math.abs(s)/Sh*(ry-ey);const p=pt3(a,s,0);
        box(g('brick'),p[0],yb-.6,p[2],.55,ry-yb+1.4,.55,ux,uz,white.clone().multiplyScalar(.92),1.4)}
    }else{
      // flat roof + parapet + rooftop units
      const G=g('flat');
      for(const ring0 of outer){
        let ring=ring0.slice();if(eqp(ring[0],ring[ring.length-1]))ring.pop();if(ring.length<3)continue;
        const holes=b.rings.inner.filter(hr=>inter(bbOf(hr),bbOf(ring))).map(hr=>{const x=hr.slice();if(eqp(x[0],x[x.length-1]))x.pop();return x.map(p=>new THREE.Vector2(p[0],p[1]))});
        const contour=ring.map(p=>new THREE.Vector2(p[0],p[1]));
        let idx;try{idx=THREE.ShapeUtils.triangulateShape(contour,holes)}catch(e){continue}
        const all=contour.concat(...holes),y=wallTop;
        for(const [i,j,k] of idx){const a=all[i],bb=all[j],d=all[k];tri(G,[a.x,y,a.y],[bb.x,y,bb.y],[d.x,y,d.y],[a.x/5,a.y/5],[bb.x/5,bb.y/5],[d.x/5,d.y/5],rc,null,[0,1,0])}
        if(areaOf(ring)<0)ring.reverse();
        const ph=st==='ind'?.35:.7;
        for(let i=0;i<ring.length;i++){const p=ring[i],q=ring[(i+1)%ring.length],len=Math.hypot(q[0]-p[0],q[1]-p[1]);if(len<.05)continue;const n=[(q[1]-p[1])/len,-(q[0]-p[0])/len];
          wall(g('plinth'),p,q,wallTop,wallTop+ph,0,len/2,0,ph/2,plc,n);
          const pi=[p[0]-n[0]*.25,p[1]-n[1]*.25],qi=[q[0]-n[0]*.25,q[1]-n[1]*.25];
          wall(g('plinth'),qi,pi,wallTop,wallTop+ph,0,len/2,0,ph/2,plc,[-n[0],-n[1]]);
          quad(g('plinth'),[p[0],wallTop+ph,p[1]],[q[0],wallTop+ph,q[1]],[qi[0],wallTop+ph,qi[1]],[pi[0],wallTop+ph,pi[1]],[0,0],[0,0],[0,0],[0,0],plc,[0,1,0]);}
      }
      if(b.size>220&&outer.length===1){
        const n=Math.min(4,1+Math.floor(b.size/500)),R=rng(Math.abs(b.id));
        const ob2=obb(outer[0]);
        if(ob2)for(let k=0;k<n;k++){const a=(R()-.5)*ob2.L*1.2,s=(R()-.5)*ob2.Sh*1.2,x=ob2.cx+ob2.ux*a-ob2.uz*s,z=ob2.cz+ob2.uz*a+ob2.ux*s;
          if(!pip(x,z,b.rings))continue;box(g('unit'),x,wallTop,z,1.6+R()*2.4,1+R()*1.2,1.4+R()*1.8,ob2.ux,ob2.uz,white,1.5)}
      }
    }
  }
  const out=[];
  for(const k in B){const G=B[k];if(!G.P.length)continue;
    const geo=new THREE.BufferGeometry();
    geo.setAttribute('position',new THREE.Float32BufferAttribute(G.P,3));geo.setAttribute('normal',new THREE.Float32BufferAttribute(G.N,3));
    geo.setAttribute('uv',new THREE.Float32BufferAttribute(G.U,2));geo.setAttribute('color',new THREE.Float32BufferAttribute(G.C,3));
    const m=new THREE.Mesh(geo,FAC[k]);m.castShadow=k!=='rail';m.receiveShadow=true;out.push(m)}
  return out;
}

/* ---------------- facade & roof textures ---------------- */
const FAC={};
function facadeTextures(){
  const T=(draw,w=256,h=256)=>{const t=canvasTex(w,h,draw,true);return t};
  const plaster=(g,w,h,base='#f4f2ee',amt=10)=>{grain(g,w,h,base,amt);g.fillStyle='rgba(0,0,0,.012)';for(let k=0;k<14;k++){g.beginPath();g.arc(Math.random()*w,Math.random()*h,30+Math.random()*50,0,7);g.fill()}const gr=g.createLinearGradient(0,0,0,h);gr.addColorStop(0,'rgba(0,0,0,0)');gr.addColorStop(1,'rgba(0,0,0,.05)');g.fillStyle=gr;g.fillRect(0,0,w,h)};
  const glass=(g,x,y,w,h,sky=.35)=>{const gr=g.createLinearGradient(x,y,x+w*.4,y+h);gr.addColorStop(0,'#5d7387');gr.addColorStop(.45,'#2a3644');gr.addColorStop(1,'#1c242e');g.fillStyle=gr;g.fillRect(x,y,w,h);
    g.fillStyle=`rgba(200,220,235,${sky})`;g.beginPath();g.moveTo(x,y+h*.55);g.lineTo(x+w*.55,y);g.lineTo(x+w*.75,y);g.lineTo(x,y+h*.85);g.closePath();g.fill()};
  const win=(g,x,y,w,h,frame='#f5f5f2',cross=true,light=false)=>{
    g.fillStyle='rgba(0,0,0,.25)';g.fillRect(x-3,y-3,w+6,h+8);
    g.fillStyle=frame;g.fillRect(x-7,y-7,w+14,h+14);
    glass(g,x,y,w,h);
    if(light){g.fillStyle='rgba(255,222,160,.35)';g.fillRect(x,y,w,h)}
    g.fillStyle=frame;if(cross){g.fillRect(x+w/2-3,y,6,h);g.fillRect(x,y+h*.36,w,5)}
    g.fillStyle='rgba(255,255,255,.08)';g.fillRect(x,y,w,4);
  };
  // house: one bay = 3 m wide, 1 floor = 3.1 m
  FAC.house=T((g,w,h)=>{plaster(g,w,h);win(g,82,62,92,112);g.fillStyle='#d9d6cf';g.fillRect(70,190,116,10);g.fillStyle='rgba(0,0,0,.18)';g.fillRect(70,200,116,4)});
  FAC.house2=T((g,w,h)=>{plaster(g,w,h);win(g,86,62,84,112,'#fbfaf6');
    for(const x of [50,184]){g.fillStyle='#3f5a46';g.fillRect(x,56,24,124);g.fillStyle='rgba(0,0,0,.25)';for(let y=62;y<176;y+=8)g.fillRect(x+2,y,20,2)}
    g.fillStyle='#d9d6cf';g.fillRect(76,190,104,9)});
  FAC.apart=T((g,w,h)=>{plaster(g,w,h,'#f2f0ec',8);g.fillStyle='rgba(0,0,0,.08)';g.fillRect(0,236,w,20);win(g,52,54,152,132,'#4a4f55',true);g.fillStyle='#c9c6bf';g.fillRect(46,196,164,8)});
  FAC.brick=T((g,w,h)=>{g.fillStyle='#d8d2c8';g.fillRect(0,0,w,h);const bh=10.5,bw=30;
    for(let row=0;row*bh<h;row++)for(let col=-1;col*bw<w;col++){const x=col*bw+(row%2?bw/2:0),y=row*bh;const v=Math.random();g.fillStyle=`rgb(${150+v*40|0},${70+v*25|0},${52+v*20|0})`;g.fillRect(x+1.5,y+1.5,bw-3,bh-3)}
    g.fillStyle='#e8e2d6';g.fillRect(60,44,136,10);win(g,74,64,108,120,'#f1efe9');g.fillStyle='#e8e2d6';g.fillRect(68,192,120,8)});
  FAC.glass=T((g,w,h)=>{const gr=g.createLinearGradient(0,0,w,h);gr.addColorStop(0,'#8aa6bb');gr.addColorStop(.5,'#3f5568');gr.addColorStop(1,'#2a3846');g.fillStyle=gr;g.fillRect(0,0,w,h);
    g.fillStyle='rgba(220,235,245,.18)';g.beginPath();g.moveTo(0,h*.7);g.lineTo(w*.6,0);g.lineTo(w,0);g.lineTo(0,h);g.fill();
    g.fillStyle='#b9c2c9';for(let x=0;x<=w;x+=w/3)g.fillRect(x-3,0,6,h);g.fillStyle='#9aa4ac';g.fillRect(0,h-26,w,26);g.fillRect(0,0,w,4)});
  FAC.ind=T((g,w,h)=>{for(let x=0;x<w;x+=16){const gr=g.createLinearGradient(x,0,x+16,0);gr.addColorStop(0,'#f2f3f3');gr.addColorStop(.5,'#c7cacc');gr.addColorStop(1,'#eceeee');g.fillStyle=gr;g.fillRect(x,0,16,h)}
    g.fillStyle='rgba(0,0,0,.06)';for(let k=0;k<12;k++)g.fillRect(Math.random()*w,Math.random()*h,2,40+Math.random()*60);
    glass(g,0,22,w,34,.2);g.fillStyle='#9ea4a8';for(let x=0;x<w;x+=64)g.fillRect(x,22,4,34)});
  FAC.stone=T((g,w,h)=>{g.fillStyle='#b9a88a';g.fillRect(0,0,w,h);const bh=21;
    for(let row=0;row*bh<h;row++)for(let col=-1;col*48<w;col++){const x=col*48+(row%2?24:0),y=row*bh,v=Math.random();g.fillStyle=`rgb(${205+v*30|0},${188+v*28|0},${152+v*25|0})`;g.fillRect(x+1.5,y+1.5,45,bh-3)}
    const x=98,y=26,ww=60,hh=190;g.fillStyle='#7d6a52';g.beginPath();g.moveTo(x-8,y+hh+6);g.lineTo(x-8,y+30);g.arc(x+ww/2,y+30,ww/2+8,Math.PI,0);g.lineTo(x+ww+8,y+hh+6);g.fill();
    g.save();g.beginPath();g.moveTo(x,y+hh);g.lineTo(x,y+30);g.arc(x+ww/2,y+30,ww/2,Math.PI,0);g.lineTo(x+ww,y+hh);g.closePath();g.clip();
    const cols=['#3c5a7a','#7a3c3c','#c9a84a','#3c6a4a','#2c3c5a'];for(let yy=y;yy<y+hh;yy+=14)for(let xx=x;xx<x+ww;xx+=14){g.fillStyle=cols[(Math.random()*cols.length)|0];g.fillRect(xx,yy,13,13)}
    g.fillStyle='rgba(20,20,20,.55)';for(let yy=y;yy<y+hh;yy+=14)g.fillRect(x,yy,ww,2);for(let xx=x;xx<x+ww;xx+=14)g.fillRect(xx,y,2,hh);g.restore()});
  FAC.shop=T((g,w,h)=>{plaster(g,w,h,'#e9e6e0',8);const sc=['#2f4f6f','#7a2e2e','#2e5e46','#5a4a2e','#333840'][(Math.random()*5)|0];g.fillStyle=sc;g.fillRect(0,10,w,34);
    g.fillStyle='rgba(255,255,255,.65)';for(let k=0;k<5;k++)g.fillRect(30+k*40,22,26,10);
    g.fillStyle='#2b2e33';g.fillRect(14,56,w-28,h-62);glass(g,22,62,w-44,h-74,.28);g.fillStyle='rgba(255,226,170,.28)';g.fillRect(22,62,w-44,h-74);g.fillStyle='#2b2e33';g.fillRect(w/2-3,62,6,h-74)});
  FAC.door=T((g,w,h)=>{g.fillStyle='#e6e2da';g.fillRect(0,0,w,h);g.fillStyle='#5b3d26';g.fillRect(12,18,w-24,h-18);
    g.fillStyle='rgba(0,0,0,.25)';g.fillRect(24,34,w-48,h*.38);g.fillRect(24,h*.52,w-48,h*.4);glass(g,30,40,w-60,h*.3,.25);
    g.fillStyle='#d8c27a';g.fillRect(w-36,h*.55,10,4)},128,256);
  FAC.plinth=T((g,w,h)=>{grain(g,w,h,'#c4c1bb',22)});
  FAC.rail=T((g,w,h)=>{g.fillStyle='#dcdad6';g.fillRect(0,0,w,h);g.fillStyle='#bdbab4';g.fillRect(0,0,w,18)});
  FAC.unit=T((g,w,h)=>{grain(g,w,h,'#c9ccce',10);g.fillStyle='rgba(0,0,0,.22)';for(let y=20;y<h;y+=22)g.fillRect(10,y,w-20,6);g.beginPath();g.arc(w*.7,h*.35,40,0,7);g.fillStyle='#3d4247';g.fill()});
  FAC.roof=T((g,w,h)=>{g.fillStyle='#e8e6e2';g.fillRect(0,0,w,h);const rows=8,rh=h/rows,tw=w/8;
    for(let r=0;r<rows;r++)for(let k=-1;k<9;k++){const x=k*tw+(r%2?tw/2:0),y=r*rh,v=.82+Math.random()*.18;
      const gr=g.createLinearGradient(0,y,0,y+rh);gr.addColorStop(0,`rgba(${255*v|0},${255*v|0},${255*v|0},1)`);gr.addColorStop(1,`rgba(${190*v|0},${190*v|0},${190*v|0},1)`);
      g.fillStyle=gr;g.beginPath();g.moveTo(x+1,y);g.lineTo(x+tw-1,y);g.lineTo(x+tw-1,y+rh*.75);g.quadraticCurveTo(x+tw/2,y+rh*1.08,x+1,y+rh*.75);g.closePath();g.fill()}
    g.fillStyle='rgba(0,0,0,.12)';for(let r=0;r<rows;r++)g.fillRect(0,r*rh,w,2)});
  FAC.flat=T((g,w,h)=>{grain(g,w,h,'#d7d6d2',40);g.fillStyle='rgba(0,0,0,.05)';for(let k=0;k<20;k++){g.beginPath();g.arc(Math.random()*w,Math.random()*h,10+Math.random()*40,0,7);g.fill()}});
  const L=(t,o={})=>new THREE.MeshLambertMaterial({map:t,vertexColors:true,...o});
  for(const k of Object.keys(FAC))FAC[k]=k==='glass'?new THREE.MeshPhongMaterial({map:FAC[k],vertexColors:true,shininess:90,specular:'#9fb6c8'}):L(FAC[k],k==='roof'||k==='plinth'||k==='rail'?{side:THREE.DoubleSide}:{});
  for(const k in FAC)FAC[k].userData.shared=true;
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

/* ---------------- water & lamps ---------------- */
function buildWater(c,items){
  const P=[];c.waters=c.waters||[];
  const inC=(x,z)=>x>=c.x0&&x<c.x0+CH&&z>=c.z0&&z<c.z0+CH;
  for(const w of items){
    if(w.kind==='area'&&w.st.water&&!w.wbuilt&&inC((w.bb[0]+w.bb[2])/2,(w.bb[1]+w.bb[3])/2)){
      w.wbuilt=true;c.waters.push(w);
      for(const ring0 of w.rings.outer){
        let ring=ring0.slice();if(eqp(ring[0],ring[ring.length-1]))ring.pop();if(ring.length<3)continue;
        let lv=1e9;for(let i=0;i<ring.length;i+=Math.max(1,ring.length/60|0))lv=Math.min(lv,height(ring[i][0],ring[i][1]));lv-=.25;
        const holes=w.rings.inner.filter(hr=>inter(bbOf(hr),bbOf(ring))).map(hr=>{const x=hr.slice();if(eqp(x[0],x[x.length-1]))x.pop();return x.map(p=>new THREE.Vector2(p[0],p[1]))});
        const ct=ring.map(p=>new THREE.Vector2(p[0],p[1]));let idx;try{idx=THREE.ShapeUtils.triangulateShape(ct,holes)}catch(e){continue}
        const all=ct.concat(...holes);
        for(const [i,j,k] of idx){let a=all[i],b=all[j],d=all[k];if((b.x-a.x)*(d.y-a.y)-(b.y-a.y)*(d.x-a.x)>0)[b,d]=[d,b];P.push(a.x,lv,a.y,b.x,lv,b.y,d.x,lv,d.y)}
      }
    }
    if(w.kind==='wline'&&w.w>=2.5){
      if(!w.oL){w.oL=offsetLine(w.pts,w.w/2);w.oR=offsetLine(w.pts,-w.w/2)}
      for(let k=0;k<w.pts.length-1;k++){const a=w.pts[k],b=w.pts[k+1];if(!inC((a[0]+b[0])/2,(a[1]+b[1])/2))continue;
        const ya=height(a[0],a[1])-.3,yb=height(b[0],b[1])-.3,L0=w.oL[k],L1=w.oL[k+1],R0=w.oR[k],R1=w.oR[k+1];
        const tr=(p,q,r,yp,yq,yr)=>{if((q[0]-p[0])*(r[1]-p[1])-(q[1]-p[1])*(r[0]-p[0])>0){[q,r]=[r,q];[yq,yr]=[yr,yq]}P.push(p[0],yp,p[1],q[0],yq,q[1],r[0],yr,r[1])};
        tr(L0,R0,R1,ya,ya,yb);tr(L0,R1,L1,ya,yb,yb);}
    }
  }
  if(!P.length)return null;
  const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(P,3));g.computeVertexNormals();
  const m=new THREE.Mesh(g,MAT.water);m.receiveShadow=true;return m;
}
function buildLamps(c,items,cells){
  const L=[];
  for(const r of items){if(r.kind!=='road'||!isSidewalkRoad(r))continue;
    let acc=hash(r.id)*30,side=1;
    for(let k=0;k<r.pts.length-1;k++){const a=r.pts[k],b=r.pts[k+1],len=Math.hypot(b[0]-a[0],b[1]-a[1]);if(len<.1)continue;const dx=(b[0]-a[0])/len,dz=(b[1]-a[1])/len,nx=-dz,nz=dx;
      while(acc<len){const off=r.w/2+1.5,x=a[0]+dx*acc+nx*off*side,z=a[1]+dz*acc+nz*off*side;
        if(x>=c.x0&&x<c.x0+CH&&z>=c.z0&&z<c.z0+CH&&surfaceAt(x,z)!==3)L.push([x,z,Math.atan2(nz*side,-nx*side)]);
        acc+=34;side=-side}
      acc-=len}}
  if(!L.length)return null;
  const im=new THREE.InstancedMesh(MAT.lampG,MAT.lamp,L.length),M=new THREE.Matrix4(),Q=new THREE.Quaternion(),Y=new THREE.Vector3(0,1,0),Pv=new THREE.Vector3(),Sv=new THREE.Vector3(1,1,1);
  L.forEach(([x,z,yaw],i)=>{Q.setFromAxisAngle(Y,yaw);M.compose(Pv.set(x,height(x,z)-.1,z),Q,Sv);im.setMatrixAt(i,M);addCol({t:1,x,z,r:.18},c.key,cells)});
  im.castShadow=true;im.frustumCulled=false;im.userData.sharedGeo=true;return im;
}

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
  const ground=new THREE.Mesh(geo,groundMat(new THREE.MeshLambertMaterial({map:tex})));ground.position.set(c.x0+CH/2,0,c.z0+CH/2);ground.receiveShadow=true;grp.add(ground);
  const blds=items.filter(o=>o.kind==='bld'&&o.cx>=c.x0&&o.cx<c.x0+CH&&o.cz>=c.z0&&o.cz<c.z0+CH&&!o.built);
  blds.forEach(b=>b.built=true);c.blds=blds;
  for(const m of buildBuildings(c,blds,c.cells))grp.add(m);
  const wm=buildWater(c,items);if(wm)grp.add(wm);
  const lm=buildLamps(c,items,c.cells);if(lm)grp.add(lm);
  const tg=buildTrees(c,items,c.cells);if(tg)grp.add(tg);
  if(my!==gen){dispose(grp);return}
  root.add(grp);c.group=grp;c.built=true;c.tex=tex;
}
function dispose(grp){grp.traverse(o=>{if(o.geometry&&!o.userData.sharedGeo&&!o.isInstancedMesh)o.geometry.dispose();if(o.isInstancedMesh)o.dispose&&o.dispose();if(o.material&&!o.material.userData.shared&&o.material!==MAT.bld){if(o.material.map)o.material.map.dispose();o.material.dispose()}})}
function dropChunk(c){
  if(c.group){root.remove(c.group);dispose(c.group);c.group=null}
  for(const k of c.cells){const a=colGrid.get(k);if(a){const f=a.filter(x=>x.ck!==c.key);if(f.length)colGrid.set(k,f);else colGrid.delete(k)}}
  c.cells.clear();c.blds.forEach(b=>b.built=false);c.blds=[];(c.waters||[]).forEach(w=>w.wbuilt=false);c.waters=[];c.built=false;c.surf=null;c.mini=null;
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
export async function jumpTo(x,z,onStep){
  const ci=Math.round(x/CH),cj=Math.round(z/CH),my=gen;
  for(const c of chunks.values())if(c.built&&Math.max(Math.abs(c.i-ci),Math.abs(c.j-cj))>1)dropChunk(c);
  const ring=[];for(let j=cj-1;j<=cj+1;j++)for(let i=ci-1;i<=ci+1;i++)ring.push(getChunk(i,j));
  const need=ring.filter(c=>!c.data);
  if(need.length){onStep('Lade Straßen und Gebäude',.25);await fetchRegion(need)}
  const todo=ring.filter(c=>!c.built).sort((a,b)=>Math.hypot(a.i-ci,a.j-cj)-Math.hypot(b.i-ci,b.j-cj));
  for(let k=0;k<todo.length;k++){if(my!==gen)return;onStep('Baue Welt',.45+.5*k/todo.length);await new Promise(r=>setTimeout(r,0));buildChunk(todo[k])}
  onStep('Fertig',1);
}
export function builtChunks(){const a=[];for(const c of chunks.values())if(c.built&&c.mini)a.push(c);return a}
export function spawnPoint(){
  const car=w=>!/^(track|service|pedestrian|raceway)$/.test(w.tags.highway)&&w.tags.access!=='no';
  const r=nearestRoad(0,0,450,car)||nearestRoad(0,0,450);
  if(r)return {x:r.x,z:r.z,th:Math.atan2(r.dx,r.dz),name:r.w.tags.name||null};
  return {x:0,z:0,th:0,name:null};
}
