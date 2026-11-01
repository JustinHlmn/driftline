// Projection, OpenStreetMap (Overpass) and elevation (Terrarium tiles)
export const O={lat:0,lon:0,kx:111320,kz:110574};
export function setOrigin(lat,lon){O.lat=lat;O.lon=lon;O.kx=Math.cos(lat*Math.PI/180)*111320}
export const toLocal=(lat,lon)=>[(lon-O.lon)*O.kx,-(lat-O.lat)*O.kz];
export const toLatLon=(x,z)=>[O.lat-z/O.kz,O.lon+x/O.kx];

const ENDPOINTS=[
  'https://overpass-api.de/api/interpreter',
  'https://overpass.private.coffee/api/interpreter',
  'https://overpass.kumi.systems/api/interpreter',
];
let ep=0;
export async function fetchOSM(x0,z0,x1,z1,signal){
  const [n,w]=toLatLon(x0,z0),[s,e]=toLatLon(x1,z1);
  const b=`${s.toFixed(6)},${w.toFixed(6)},${n.toFixed(6)},${e.toFixed(6)}`;
  const q=`[out:json][timeout:50];(
way["highway"](${b});
way["building"](${b});relation["building"](${b});
way["landuse"](${b});relation["landuse"](${b});
way["natural"](${b});relation["natural"~"^(water|wood|scrub|wetland|grassland|heath|sand|beach)$"](${b});
way["leisure"](${b});relation["leisure"~"^(park|garden|golf_course|nature_reserve)$"](${b});
way["amenity"="parking"](${b});
way["waterway"](${b});relation["waterway"="riverbank"](${b});relation["water"](${b});
way["railway"~"^(rail|tram|light_rail|narrow_gauge|subway)$"](${b});
way["area:highway"](${b});
node["natural"="tree"](${b});
);out geom qt;`;
  let last;
  for(let k=0;k<ENDPOINTS.length;k++){
    const url=ENDPOINTS[(ep+k)%ENDPOINTS.length];
    try{
      const r=await fetch(url,{method:'POST',body:'data='+encodeURIComponent(q),headers:{'Content-Type':'application/x-www-form-urlencoded'},signal});
      if(!r.ok){last=new Error('Server '+r.status);continue}
      const j=await r.json();
      if(j.remark&&/runtime error|timed out/i.test(j.remark)&&!(j.elements&&j.elements.length)){last=new Error('Zeitüberschreitung');continue}
      ep=(ep+k)%ENDPOINTS.length;
      return j.elements||[];
    }catch(err){if(signal&&signal.aborted)throw err;last=err}
  }
  throw last||new Error('Kartendaten nicht erreichbar');
}

/* ---- elevation: AWS Terrain Tiles (Terrarium encoding), zoom 14 ≈ 6 m per pixel in Germany ---- */
const EZ=14,N=2**EZ,tiles=new Map();
const lon2x=lon=>(lon+180)/360*N;
const lat2y=lat=>{const r=lat*Math.PI/180;return (1-Math.log(Math.tan(r)+1/Math.cos(r))/Math.PI)/2*N};
function tile(tx,ty){
  const k=tx+','+ty;let t=tiles.get(k);if(t)return t.p;
  t={d:null};tiles.set(k,t);
  t.p=new Promise(res=>{
    const img=new Image();img.crossOrigin='anonymous';
    img.onload=()=>{try{const c=document.createElement('canvas');c.width=c.height=256;const g=c.getContext('2d',{willReadFrequently:true});g.drawImage(img,0,0);
      const d=g.getImageData(0,0,256,256).data,f=new Float32Array(65536);for(let i=0;i<65536;i++)f[i]=d[i*4]*256+d[i*4+1]+d[i*4+2]/256-32768;t.d=f}catch(e){t.d=false}res()};
    img.onerror=()=>{t.d=false;res()};
    img.src=`https://s3.amazonaws.com/elevation-tiles-prod/terrarium/${EZ}/${tx}/${ty}.png`;
  });
  return t.p;
}
export function ensureElev(x0,z0,x1,z1){
  const [n,w]=toLatLon(x0,z0),[s,e]=toLatLon(x1,z1);
  const ps=[];
  for(let tx=Math.floor(lon2x(w));tx<=Math.floor(lon2x(e));tx++)for(let ty=Math.floor(lat2y(n));ty<=Math.floor(lat2y(s));ty++)ps.push(tile(tx,ty));
  return Promise.all(ps);
}
function px(t,x,y){return t.d[Math.max(0,Math.min(255,y))*256+Math.max(0,Math.min(255,x))]}
export function demAt(lat,lon){
  const fx=lon2x(lon),fy=lat2y(lat),tx=Math.floor(fx),ty=Math.floor(fy);
  const t=tiles.get(tx+','+ty);if(!t||!t.d)return null;
  const x=(fx-tx)*256-.5,y=(fy-ty)*256-.5,ix=Math.floor(x),iy=Math.floor(y),ax=x-ix,ay=y-iy;
  const a=px(t,ix,iy),b=px(t,ix+1,iy),c=px(t,ix,iy+1),d=px(t,ix+1,iy+1);
  const v=(a*(1-ax)+b*ax)*(1-ay)+(c*(1-ax)+d*ax)*ay;
  return v<-500?null:v;
}

/* ---- geocoding (Nominatim) ---- */
const NOM='https://nominatim.openstreetmap.org';
export async function search(q){
  const r=await fetch(`${NOM}/search?format=jsonv2&limit=6&addressdetails=1&accept-language=de&q=${encodeURIComponent(q)}`);
  if(!r.ok)throw new Error('Suche nicht erreichbar');return r.json();
}
export async function reverse(lat,lon){
  try{const r=await fetch(`${NOM}/reverse?format=jsonv2&zoom=17&addressdetails=1&accept-language=de&lat=${lat}&lon=${lon}`);if(!r.ok)return null;return r.json()}catch(e){return null}
}
export function shortName(res){
  if(!res)return null;const a=res.address||{};
  const street=a.road||a.pedestrian||a.footway||a.square||a.hamlet||'';
  const place=a.village||a.town||a.city||a.municipality||a.suburb||a.county||'';
  const s=[street&&(street+(a.house_number?' '+a.house_number:'')),place].filter(Boolean).join(', ');
  return s||res.name||(res.display_name||'').split(',').slice(0,2).join(',');
}
