// Driftline — drift through the real world. Map data © OpenStreetMap contributors (ODbL).
import {clamp,lerp,nextFrame} from './util.js';
import {setOrigin,search,reverse,shortName} from './geo.js';
import {initWorld,loadArea,unloadAll,updateWorld,height,surfaceAt,nearestRoad,placeName,collidersNear,rayWalls,builtChunks,spawnPoint,CH,W} from './world.js';

const THREE=window.THREE;
const $=id=>document.getElementById(id);
const store={get(k,d){try{const v=localStorage.getItem(k);return v==null?d:JSON.parse(v)}catch(e){return d}},set(k,v){try{localStorage.setItem(k,JSON.stringify(v))}catch(e){}}};

/* ================= three setup ================= */
const canvas=$('view');
let renderer;
try{renderer=new THREE.WebGLRenderer({canvas,antialias:true,powerPreference:'high-performance'})}
catch(e){$('pickErr').textContent='WebGL ist in diesem Browser nicht verfügbar.';$('pickErr').hidden=false;throw e}
const DPR=Math.min(window.devicePixelRatio||1,1.6);
renderer.setPixelRatio(DPR);
renderer.shadowMap.enabled=true;
renderer.shadowMap.type=THREE.PCFSoftShadowMap;
const scene=new THREE.Scene();
const FOGC=new THREE.Color('#d6c6ab');
scene.fog=new THREE.Fog(FOGC,170,560);
const camera=new THREE.PerspectiveCamera(60,1,0.3,3000);
const SUN=new THREE.Vector3(-0.62,0.42,-0.66).normalize();
scene.add(new THREE.HemisphereLight('#c9dcff','#5e6b44',0.64));
const sunL=new THREE.DirectionalLight('#ffdcb0',1.02);
sunL.castShadow=true;sunL.shadow.mapSize.set(2048,2048);
{const sc=sunL.shadow.camera;sc.left=-70;sc.right=70;sc.top=70;sc.bottom=-70;sc.near=10;sc.far=600}
sunL.shadow.bias=-0.0006;sunL.shadow.normalBias=0.04;
scene.add(sunL);scene.add(sunL.target);
const sky=(()=>{
  const g=new THREE.SphereGeometry(1500,32,16);
  const m=new THREE.ShaderMaterial({side:THREE.BackSide,depthWrite:false,fog:false,
    uniforms:{top:{value:new THREE.Color('#4f7fc4')},mid:{value:new THREE.Color('#a9c2dd')},hor:{value:FOGC},sun:{value:SUN}},
    vertexShader:`varying vec3 vP;void main(){vP=normalize(position);gl_Position=projectionMatrix*modelViewMatrix*vec4(position,1.0);}`,
    fragmentShader:`uniform vec3 top,mid,hor,sun;varying vec3 vP;void main(){float h=vP.y;vec3 c=mix(hor,mid,smoothstep(-0.02,0.12,h));c=mix(c,top,smoothstep(0.12,0.6,h));float s=max(dot(vP,sun),0.0);c+=vec3(1.0,0.75,0.45)*pow(s,8.0)*0.35+vec3(1.0,0.95,0.85)*pow(s,900.0)*1.2;gl_FragColor=vec4(c,1.0);}`});
  const s=new THREE.Mesh(g,m);s.renderOrder=-1;s.frustumCulled=false;scene.add(s);return s;
})();
initWorld(scene,renderer);
let state='pick';
function toast(t,cls){toastEl.textContent=t;toastEl.className='toast '+(cls||'');toastEl.hidden=false;toastEl.style.opacity=1;toastT=1.6}
let toastT=0;const toastEl=$('toast');

/* ================= car model ================= */
const PRESETS=[
  {name:'Kaze 86',  desc:'Leicht und verspielt', mass:1150,power:205000,fmax:8200, grip:1.00,cs:68000,w:1.76,spoiler:0},
  {name:'Ronin S15',desc:'Der Drift-Klassiker',  mass:1240,power:300000,fmax:10200, grip:1.00,cs:74000,w:1.80,spoiler:1},
  {name:'Mammut V8',desc:'Viel Druck, viel Rauch',mass:1460,power:400000,fmax:12800,grip:1.02,cs:84000,w:1.88,spoiler:2},
];
const PAINTS=['#e9e7e1','#ff6a1a','#1f4fd6','#c3172b','#1b1d22','#2f8f5b','#f2c230'];
let sel=1, paint=1;
const CS=0.82; // visual car scale
const carRoot=new THREE.Group(), carBody=new THREE.Group();carRoot.add(carBody);scene.add(carRoot);carRoot.scale.setScalar(CS);
const paintMat=new THREE.MeshPhongMaterial({color:PAINTS[paint],shininess:110,specular:'#ffffff'});
const glassMat=new THREE.MeshPhongMaterial({color:'#11161d',shininess:140,specular:'#9fb4c8'});
const darkMat=new THREE.MeshLambertMaterial({color:'#17181a'});
const tailMat=new THREE.MeshBasicMaterial({color:'#7a0f14'});
const headMat=new THREE.MeshBasicMaterial({color:'#fff8e6'});
const wheels=[];
function buildCar(){
  while(carBody.children.length)carBody.remove(carBody.children[0]);
  wheels.forEach(w=>carRoot.remove(w.pivot));wheels.length=0;
  const p=PRESETS[sel],W=p.w;
  const box=(w,h,d,mat,x,y,z)=>{const m=new THREE.Mesh(new THREE.BoxGeometry(w,h,d),mat);m.position.set(x,y,z);m.castShadow=true;carBody.add(m);return m};
  box(W,0.5,4.35,paintMat,0,0.58,0);
  box(W-0.06,0.18,1.2,paintMat,0,0.9,1.45).rotation.x=0.06;
  box(W-0.06,0.14,0.9,paintMat,0,0.88,-1.65);
  const cab=box(W-0.24,0.5,2.0,glassMat,0,1.08,-0.25);
  box(W-0.32,0.07,1.45,paintMat,0,1.36,-0.32);
  box(W+0.02,0.22,0.25,darkMat,0,0.42,2.15);
  box(W+0.02,0.24,0.25,darkMat,0,0.42,-2.15);
  box(W*0.92,0.2,0.4,darkMat,0,0.24,0);
  [-1,1].forEach(s=>{
    box(0.36,0.1,0.06,headMat,s*(W/2-0.3),0.72,2.17);
    box(0.42,0.11,0.06,tailMat,s*(W/2-0.28),0.76,-2.18);
    box(0.18,0.1,0.25,darkMat,s*(W/2+0.02),1.02,0.65);
  });
  if(p.spoiler){
    const h=p.spoiler===2?0.08:0.22;
    box(W-0.1,0.05,0.34,darkMat,0,1.0+h,-1.95);
    [-1,1].forEach(s=>box(0.05,h,0.12,darkMat,s*(W/2-0.3),0.95+h/2,-1.95));
  }
  const tg=new THREE.CylinderGeometry(0.33,0.33,0.24,18);tg.rotateZ(Math.PI/2);
  const rg=new THREE.CylinderGeometry(0.22,0.22,0.26,12);rg.rotateZ(Math.PI/2);
  const tireM=new THREE.MeshLambertMaterial({color:'#141414'}),rimM=new THREE.MeshPhongMaterial({color:'#b9bcc0',shininess:80});
  for(const [x,z,front] of [[1,1.32,1],[-1,1.32,1],[1,-1.35,0],[-1,-1.35,0]]){
    const pivot=new THREE.Group();pivot.position.set(x*(W/2-0.12),0.33,z);
    const spin=new THREE.Group();pivot.add(spin);
    const t=new THREE.Mesh(tg,tireM);t.castShadow=true;spin.add(t);
    const r=new THREE.Mesh(rg,rimM);spin.add(r);
    for(let k=0;k<5;k++){const s=new THREE.Mesh(new THREE.BoxGeometry(0.27,0.05,0.05),darkMat);s.position.x=x*0.13;s.rotation.x=k*Math.PI*2/5;s.geometry.translate(0,0.1,0);spin.add(s)}
    carRoot.add(pivot);wheels.push({pivot,spin,front});
  }
  paintMat.color.set(PAINTS[paint]);
}

/* ================= car physics ================= */
const car={x:0,z:0,th:Math.PI/2,vx:0,vz:0,w:0,steer:0,ax:0,ay:0,thr:0,brk:0,gear:1,rpm:900,slide:0,u:0,v:0,spin:false,armed:false,gripT:0,vRate:0,pitch:0,roll:0,y:0};
let assist=true;
const input={steer:0,thr:0,brk:0,hand:false};
const GEARS=[0,15,27,39,51,64,85];
function grad(x,z){const e=1;return {x:(height(x+e,z)-height(x-e,z))/(2*e),z:(height(x,z+e)-height(x,z-e))/(2*e)}}
function physics(dt){
  const P=PRESETS[sel],m=P.mass,g=9.81,WB=2.6;
  const sf=surfaceAt(car.x,car.z),onRoad=sf===2,surf=[0.62,0.8,1,0.42][sf]*P.grip;car.sf=sf;
  let sn=Math.sin(car.th),cs=Math.cos(car.th);
  let u=car.vx*sn+car.vz*cs,v=car.vx*cs-car.vz*sn;
  const spd=Math.hypot(car.vx,car.vz);
  const slip=Math.atan2(v,Math.max(Math.abs(u),0.5));
  // steering (wheel angle, speed sensitive, smooth)
  const steerMax=0.5-0.32*Math.min(1,spd/55);
  const tgt=input.steer*steerMax;
  const sr=(input.steer===0?6:4.2)*dt;
  car.steer+=clamp(tgt-car.steer,-sr,sr);
  // drift state: only the handbrake starts a drift
  if(input.hand&&spd>8)car.armed=true;
  if(car.armed&&!input.hand&&Math.abs(slip)<0.09){car.gripT+=dt;if(car.gripT>0.25)car.armed=false}else car.gripT=0;
  if(spd<5)car.armed=false;
  // yaw
  let wT,resp;
  if(!car.armed){
    wT=u*Math.tan(car.steer)/WB;
    const wMax=g*surf*1.05/Math.max(spd,3);
    wT=clamp(wT,-wMax,wMax);resp=10;
  }else{
    const restore=(assist?1.6:1.0)*(input.thr>0.5?0.7:2.4);
    wT=car.vRate+input.steer*1.3+slip*restore;
    if(input.hand)wT+=input.steer*0.8;
    if(Math.abs(slip)>1.05)wT+=slip*4;
    resp=4.5;
  }
  car.w+=(wT-car.w)*Math.min(1,dt*resp);
  if(car.armed){const vis=clamp(-slip*0.75+input.steer*0.2,-0.62,0.62);car.steer+=(vis-car.steer)*Math.min(1,dt*8)}
  car.th+=car.w*dt;
  sn=Math.sin(car.th);cs=Math.cos(car.th);
  u=car.vx*sn+car.vz*cs;v=car.vx*cs-car.vz*sn;
  // longitudinal
  const sg=u>0.3?1:u<-0.3?-1:0;
  const reverse=input.brk>0.1&&u<1&&input.thr<0.1;
  let acc=0;
  if(reverse)acc=u>-8?-5*input.brk:0;
  else{
    acc=input.thr*Math.min(P.fmax,P.power/Math.max(Math.abs(u),1))/m*[0.7,0.85,1,0.45][sf];
    acc-=sg*input.brk*9.5;
  }
  if(u<-0.5&&input.thr>0)acc=7*input.thr;
  if(input.hand)acc-=sg*3.2;
  const gr=grad(car.x,car.z),gF=gr.x*sn+gr.z*cs,gL=gr.x*cs-gr.z*sn;
  acc-=(0.3*u*Math.abs(u)+[220,70,14,1100][sf]*u)/m+g*gF;
  if(car.armed)acc-=sg*Math.abs(Math.sin(slip))*(input.thr>0.5?1.5:4);
  const u0=u;u+=acc*dt;
  if(sg!==0&&Math.sign(u)!==sg&&input.thr<0.05&&!reverse)u=0;
  // lateral grip pulls velocity onto the heading
  const grip=car.armed?(input.hand?0.55:0.9+(1-input.thr)*2.0)*surf:11*surf;
  v*=Math.exp(-grip*dt);
  v-=g*gL*dt;
  if(spd<1.2&&input.thr<0.05&&!reverse){u*=Math.max(0,1-4*dt);v*=Math.max(0,1-4*dt)}
  const oldDir=Math.atan2(car.vx,car.vz);
  car.vx=u*sn+v*cs;car.vz=u*cs-v*sn;
  const nd=Math.atan2(car.vx,car.vz);
  car.vRate=spd>2?Math.atan2(Math.sin(nd-oldDir),Math.cos(nd-oldDir))/dt:0;
  car.x+=car.vx*dt;car.z+=car.vz*dt;
  car.ax=(u-u0)/dt;car.ay=u*car.w;
  car.u=u;car.v=v;car.onRoad=onRoad;
  car.spin=car.armed&&input.thr>0.7&&spd<35;
  // gears + rpm
  const au=Math.abs(u);let gi=1;while(gi<GEARS.length-1&&au>GEARS[gi])gi++;
  car.gear=reverse?-1:gi;
  const lo=GEARS[gi-1],hi=GEARS[gi];
  let rpm=1200+(au-lo)/(hi-lo)*6200;
  if(car.spin)rpm=Math.min(7900,rpm+2600*input.thr);
  if(spd<1)rpm=900+input.thr*5800;
  car.rpm=lerp(car.rpm,clamp(rpm,850,8000),Math.min(1,dt*10));
  // slide intensity
  const sl=Math.abs(Math.atan2(car.v,Math.max(Math.abs(car.u),.5)));
  car.slide=(car.armed?clamp((sl-.1)*2.6,0,1.2):0)+(input.hand&&spd>3?.5:0);
  if(spd<2.5)car.slide=0;
  car.onRoad=onRoad;
}

/* ================= collisions ================= */
let impact=0;const near=[];
function collide(){
  const sn=Math.sin(car.th),cs=Math.cos(car.th);let hit=0;
  collidersNear(car.x,car.z,near);
  for(const off of [1.2,0,-1.2]){
    let px=car.x+sn*off,pz=car.z+cs*off;const r=.85;
    for(const c of near){
      let nx,nz,pen;
      if(c.t){const dx=px-c.x,dz=pz-c.z,d=Math.hypot(dx,dz),R=r+c.r;if(d>=R||d<1e-4)continue;nx=dx/d;nz=dz/d;pen=R-d}
      else{const sx=c.x2-c.x1,sz=c.z2-c.z1,l2=sx*sx+sz*sz||1,t=clamp(((px-c.x1)*sx+(pz-c.z1)*sz)/l2,0,1),qx=c.x1+sx*t,qz=c.z1+sz*t,dx=px-qx,dz=pz-qz,d=Math.hypot(dx,dz);
        if(d>=r)continue;if(d<1e-4){const l=Math.sqrt(l2);nx=sz/l;nz=-sx/l;pen=r}else{nx=dx/d;nz=dz/d;pen=r-d}}
      car.x+=nx*pen;car.z+=nz*pen;px+=nx*pen;pz+=nz*pen;
      const vn=car.vx*nx+car.vz*nz;
      if(vn<0){car.vx-=1.3*vn*nx;car.vz-=1.3*vn*nz;car.vx*=.9;car.vz*=.9;car.w*=.5;hit=Math.max(hit,-vn)}
    }
  }
  if(hit>2.2)crash(hit);
}

/* ================= scoring ================= */
let score=0,bestCombo=0,cur=0,mult=1,driftT=0,grace=0,drifting=false;
try{bestCombo=+localStorage.getItem('driftline-best')||0}catch(e){}
function crash(s){
  impact=Math.min(1,s/12);thump(s);
  if(cur>0){toast('Kontakt! Combo weg','bad');cur=0;mult=1;driftT=0}
}
function updateScore(dt){
  const spd=Math.hypot(car.vx,car.vz);
  const ang=Math.atan2(Math.abs(car.v),Math.max(Math.abs(car.u),.1))*180/Math.PI;
  drifting=spd>8&&ang>12&&car.u>2;
  if(drifting){
    driftT+=dt;grace=0;
    mult=Math.min(6,1+Math.floor(driftT/2.2));
    cur+=dt*spd*3.6*Math.min(ang,60)/20*(car.onRoad?1:0.5);
  }else if(cur>0){
    grace+=dt;
    if(grace>1.4){
      const pts=Math.round(cur*mult);score+=pts;
      if(pts>bestCombo){bestCombo=pts;try{localStorage.setItem('driftline-best',String(bestCombo))}catch(e){}toast('+'+pts.toLocaleString('de-DE')+' · NEUER REKORD','good')}
      else toast('+'+pts.toLocaleString('de-DE')+' · SAUBER','good');
      cur=0;mult=1;driftT=0;
    }
  }
  return ang;
}

/* ================= skid marks + smoke ================= */
const SKN=5000;
const skid=new THREE.InstancedMesh(new THREE.PlaneGeometry(.26,.62).rotateX(-Math.PI/2),new THREE.MeshBasicMaterial({color:'#101010',transparent:true,opacity:.55,depthWrite:false,polygonOffset:true,polygonOffsetFactor:-6,polygonOffsetUnits:-12}),SKN);
skid.count=0;skid.frustumCulled=false;scene.add(skid);
function clearSkids(){skid.count=0;skidI=0;skid.instanceMatrix.needsUpdate=true}
let skidI=0,skidAcc=[0,0],skidLast=[null,null];
const SM=new THREE.Matrix4(),SQ=new THREE.Quaternion(),SP=new THREE.Vector3(),SS=new THREE.Vector3(1,1,1),UP=new THREE.Vector3(0,1,0);
function addSkid(x,z,yaw){
  SQ.setFromAxisAngle(UP,yaw);SM.compose(SP.set(x,height(x,z)+.09,z),SQ,SS);
  skid.setMatrixAt(skidI,SM);skidI=(skidI+1)%SKN;skid.count=Math.min(SKN,skid.count+1);skid.instanceMatrix.needsUpdate=true;
}
const PN=420;
const smokeGeo=new THREE.BufferGeometry();
const sPos=new Float32Array(PN*3),sSize=new Float32Array(PN),sAlpha=new Float32Array(PN);
smokeGeo.setAttribute('position',new THREE.BufferAttribute(sPos,3));
smokeGeo.setAttribute('aSize',new THREE.BufferAttribute(sSize,1));
smokeGeo.setAttribute('aAlpha',new THREE.BufferAttribute(sAlpha,1));
const smokeMat=new THREE.ShaderMaterial({transparent:true,depthWrite:false,uniforms:{uScale:{value:600},uColor:{value:new THREE.Color('#ece8e2')}},
  vertexShader:`attribute float aSize;attribute float aAlpha;varying float vA;uniform float uScale;void main(){vA=aAlpha;vec4 mv=modelViewMatrix*vec4(position,1.0);gl_PointSize=aSize*uScale/max(-mv.z,0.5);gl_Position=projectionMatrix*mv;}`,
  fragmentShader:`varying float vA;uniform vec3 uColor;void main(){float d=length(gl_PointCoord-0.5);float a=smoothstep(0.5,0.1,d)*vA;if(a<0.005)discard;gl_FragColor=vec4(uColor,a);}`});
const smoke=new THREE.Points(smokeGeo,smokeMat);smoke.frustumCulled=false;scene.add(smoke);
const parts=Array.from({length:PN},()=>({life:0,max:1,x:0,y:0,z:0,vx:0,vy:0,vz:0,s:1}));
let pI=0;
function emit(x,y,z,vx,vz,k){const p=parts[pI];pI=(pI+1)%PN;p.life=p.max=1.6+Math.random()*1.2;p.x=x;p.y=y;p.z=z;p.vx=vx*.25+(Math.random()-.5)*1.6;p.vz=vz*.25+(Math.random()-.5)*1.6;p.vy=.6+Math.random()*.9;p.s=.9+k*.6}
function updateSmoke(dt){
  for(let i=0;i<PN;i++){const p=parts[i];
    if(p.life>0){p.life-=dt;p.x+=p.vx*dt;p.y+=p.vy*dt;p.z+=p.vz*dt;p.vx*=1-1.2*dt;p.vz*=1-1.2*dt;p.vy*=1-.6*dt;
      const t=1-p.life/p.max;sSize[i]=p.s*(1.2+t*5);sAlpha[i]=Math.max(0,.42*(1-t)*Math.min(1,t*6));}
    else sAlpha[i]=0;
    sPos[i*3]=p.x;sPos[i*3+1]=p.y;sPos[i*3+2]=p.z;}
  smokeGeo.attributes.position.needsUpdate=true;smokeGeo.attributes.aSize.needsUpdate=true;smokeGeo.attributes.aAlpha.needsUpdate=true;
}
function effects(dt){
  const sn=Math.sin(car.th),cs=Math.cos(car.th);
  const spd=Math.hypot(car.vx,car.vz);
  const k=car.slide;
  [-1,1].forEach((s,i)=>{
    const hw=(PRESETS[sel].w/2-.12)*CS,wx=car.x-sn*1.35*CS+cs*s*hw,wz=car.z-cs*1.35*CS-sn*s*hw;
    if(k>.35&&spd>2.5){
      const lp=skidLast[i],yaw=Math.atan2(car.vx,car.vz);
      if(lp){const dx=wx-lp[0],dz=wz-lp[1],dl=Math.hypot(dx,dz);if(dl<8){for(let s2=skidAcc[i];s2<dl;s2+=.45)addSkid(lp[0]+dx*s2/dl,lp[1]+dz*s2/dl,yaw);skidAcc[i]=(skidAcc[i]-dl)%.45;if(skidAcc[i]<0)skidAcc[i]+=.45}}
      skidLast[i]=[wx,wz];
      if(car.onRoad&&Math.random()<k*1.6)emit(wx,height(wx,wz)+.3,wz,car.vx,car.vz,k);
      if(!car.onRoad&&Math.random()<k*.8){emit(wx,height(wx,wz)+.3,wz,car.vx,car.vz,k*.5)}
    }else{skidAcc[i]=0;skidLast[i]=null}
  });
}

/* ================= audio ================= */
let actx=null,eng=null,squeal=null,muted=false;
function initAudio(){
  if(actx){if(actx.state==='suspended')actx.resume();return}
  try{
    actx=new (window.AudioContext||window.webkitAudioContext)();
    const master=actx.createGain();master.gain.value=.9;master.connect(actx.destination);
    const o1=actx.createOscillator(),o2=actx.createOscillator(),f=actx.createBiquadFilter(),g=actx.createGain();
    o1.type='sawtooth';o2.type='square';f.type='lowpass';f.frequency.value=700;f.Q.value=3;g.gain.value=0;
    o1.connect(f);o2.connect(f);f.connect(g);g.connect(master);o1.start();o2.start();
    const len=actx.sampleRate*2,buf=actx.createBuffer(1,len,actx.sampleRate),d=buf.getChannelData(0);for(let i=0;i<len;i++)d[i]=Math.random()*2-1;
    const n=actx.createBufferSource();n.buffer=buf;n.loop=true;
    const bp=actx.createBiquadFilter();bp.type='bandpass';bp.frequency.value=1500;bp.Q.value=4;
    const bp2=actx.createBiquadFilter();bp2.type='peaking';bp2.frequency.value=2600;bp2.gain.value=10;
    const sg=actx.createGain();sg.gain.value=0;n.connect(bp);bp.connect(bp2);bp2.connect(sg);sg.connect(master);n.start();
    eng={o1,o2,f,g,master};squeal={bp,sg};
  }catch(e){actx=null}
}
function updateAudio(){
  if(!eng)return;const t=actx.currentTime;const on=!muted&&state==='drive';
  const fr=car.rpm/60*2;
  eng.o1.frequency.setTargetAtTime(fr,t,.03);eng.o2.frequency.setTargetAtTime(fr*.5,t,.03);
  eng.f.frequency.setTargetAtTime(300+car.rpm*.22+input.thr*600,t,.05);
  eng.g.gain.setTargetAtTime(on?.035+input.thr*.045:0,t,.08);
  const sq=on?clamp(car.slide,0,1)*(car.onRoad?.16:.03):0;
  squeal.sg.gain.setTargetAtTime(sq,t,.06);squeal.bp.frequency.setTargetAtTime(1100+Math.hypot(car.vx,car.vz)*12,t,.1);
}
function thump(s){
  if(!actx||muted)return;
  try{const len=.25,buf=actx.createBuffer(1,actx.sampleRate*len,actx.sampleRate),d=buf.getChannelData(0);for(let i=0;i<d.length;i++)d[i]=(Math.random()*2-1)*Math.pow(1-i/d.length,3);
  const src=actx.createBufferSource(),f=actx.createBiquadFilter(),g=actx.createGain();f.type='lowpass';f.frequency.value=500;g.gain.value=Math.min(.8,.15+s*.05);src.buffer=buf;src.connect(f);f.connect(g);g.connect(eng?eng.master:actx.destination);src.start()}catch(e){}
}

/* ================= camera ================= */
let camMode=0;const CAMS=['Verfolger','Nah','Haube','Vogel'];
const camPos=new THREE.Vector3(-10,4,0),look=new THREE.Vector3();
function updateCamera(dt,t){
  const sn=Math.sin(car.th),cs=Math.cos(car.th);
  const spd=Math.hypot(car.vx,car.vz);
  const cy=car.y;
  if(state==='menu'){
    const a=t*.18;camPos.set(car.x+Math.cos(a)*8.5,cy+2.6,car.z+Math.sin(a)*8.5);
    camera.position.copy(camPos);camera.lookAt(car.x,cy+.8,car.z);camera.fov=50;camera.updateProjectionMatrix();return;
  }
  let dirx=sn,dirz=cs;
  if(spd>3){const vx=car.vx/spd,vz=car.vz/spd;dirx=lerp(sn,vx,.4);dirz=lerp(cs,vz,.4);const l=Math.hypot(dirx,dirz);dirx/=l;dirz/=l}
  let des,lk,k=1-Math.exp(-7*dt);
  if(camMode===0){const pull=Math.min(1.6,spd*.03);des=new THREE.Vector3(car.x-dirx*(7+pull),cy+2.1,car.z-dirz*(7+pull));lk=new THREE.Vector3(car.x+sn*3,cy+.85,car.z+cs*3)}
  else if(camMode===1){des=new THREE.Vector3(car.x-dirx*4.8,cy+1.45,car.z-dirz*4.8);lk=new THREE.Vector3(car.x+sn*3,cy+.8,car.z+cs*3);k=1-Math.exp(-10*dt)}
  else if(camMode===2){des=new THREE.Vector3(car.x+sn*.2,cy+1.08,car.z+cs*.2);lk=new THREE.Vector3(car.x+sn*20,cy+1,car.z+cs*20);k=1}
  else{des=new THREE.Vector3(car.x-sn*6,cy+42,car.z-cs*6);lk=new THREE.Vector3(car.x+sn*4,cy,car.z+cs*4);k=1-Math.exp(-4*dt)}
  camPos.lerp(des,k);
  if(camMode<2){const f=rayWalls(car.x,car.z,camPos.x,camPos.z,camPos.y);if(f<1){const k2=Math.max(.12,f-.08);camPos.x=lerp(car.x,camPos.x,k2);camPos.z=lerp(car.z,camPos.z,k2)}}
  const gh=height(camPos.x,camPos.z)+.8;if(camPos.y<gh)camPos.y=gh;
  look.lerp(lk,camMode===2?1:Math.min(1,k*1.6));
  camera.position.copy(camPos);
  if(impact>0){camera.position.x+=(Math.random()-.5)*impact*.5;camera.position.y+=(Math.random()-.5)*impact*.4;impact=Math.max(0,impact-dt*2.5)}
  camera.lookAt(look);
  const fov=(camMode===2?70:60)+Math.min(10,spd*.18);
  camera.fov=lerp(camera.fov,fov,Math.min(1,dt*1.5));camera.updateProjectionMatrix();
}

/* ================= car visual sync ================= */
function syncCar(dt){
  const P=PRESETS[sel];
  const gr=grad(car.x,car.z),sn=Math.sin(car.th),cs=Math.cos(car.th);
  const gF=gr.x*sn+gr.z*cs,gL=gr.x*cs-gr.z*sn;
  car.y=height(car.x,car.z)+.03;
  carRoot.position.set(car.x,car.y,car.z);
  car.pitch=lerp(car.pitch,-Math.atan(gF),Math.min(1,dt*10));
  car.roll=lerp(car.roll,Math.atan(gL),Math.min(1,dt*10));
  carRoot.rotation.set(car.pitch,car.th,car.roll,'YXZ');
  carBody.rotation.x=lerp(carBody.rotation.x,clamp(-car.ax*.006,-.05,.05),Math.min(1,dt*6));
  carBody.rotation.z=lerp(carBody.rotation.z,clamp(car.ay*.007,-.06,.06),Math.min(1,dt*6));
  const r=.33*CS;
  wheels.forEach(w=>{
    if(w.front)w.pivot.rotation.y=car.steer;
    const extra=!w.front&&car.spin?input.thr*40:0,lock=!w.front&&input.hand;
    if(!lock)w.spin.rotation.x+=(car.u/r+extra)*dt;
  });
  tailMat.color.set(input.brk>.1||input.hand?'#ff2a30':'#7a0f14');
  const Y=car.y;sunL.position.set(car.x+SUN.x*200,Y+SUN.y*200,car.z+SUN.z*200);sunL.target.position.set(car.x,Y,car.z);
  sky.position.set(camera.position.x,camera.position.y,camera.position.z);
}

/* ================= input ================= */
const keys={};
const KEYMAP={KeyW:'gas',ArrowUp:'gas',KeyS:'brake',ArrowDown:'brake',KeyA:'left',ArrowLeft:'left',KeyD:'right',ArrowRight:'right',Space:'hand'};
addEventListener('keydown',e=>{
  const k=KEYMAP[e.code];if(k&&state==='drive'){keys[k]=true;e.preventDefault()}
  if(e.repeat)return;
  if(e.code==='KeyC'&&state==='drive')cycleCam();
  if(e.code==='KeyR'&&state==='drive')resetToRoad();
  if((e.code==='KeyP'||e.code==='Escape')&&(state==='drive'||state==='pause'))setPause(state==='drive');
});
addEventListener('keyup',e=>{const k=KEYMAP[e.code];if(k)keys[k]=false});
addEventListener('blur',()=>{for(const k in keys)keys[k]=false});
document.addEventListener('visibilitychange',()=>{if(document.hidden&&state==='drive')setPause(true)});
document.querySelectorAll('.tb').forEach(b=>{
  const k=b.dataset.k;const on=e=>{e.preventDefault();keys[k]=true;b.classList.add('on')};const off=()=>{keys[k]=false;b.classList.remove('on')};
  b.addEventListener('pointerdown',on);['pointerup','pointercancel','pointerleave'].forEach(t=>b.addEventListener(t,off));
});
function readInput(dt){
  let st=(keys.left?1:0)-(keys.right?1:0),th=keys.gas?1:0,br=keys.brake?1:0,hd=!!keys.hand;
  const pads=navigator.getGamepads?navigator.getGamepads():[];
  for(const p of pads){if(!p)continue;
    const ax=p.axes[0]||0;if(Math.abs(ax)>.12)st=-ax;
    if(p.buttons[7]&&p.buttons[7].value>.05)th=p.buttons[7].value;
    if(p.buttons[6]&&p.buttons[6].value>.05)br=p.buttons[6].value;
    if(p.buttons[0]&&p.buttons[0].pressed)hd=true;
    break;}
  input.steer=st;
  input.thr=th>input.thr?Math.min(th,input.thr+dt*5):Math.max(th,input.thr-dt*7);
  input.brk=br;input.hand=hd;
}


/* ================= minimap ================= */
const mini=$('mini'),mg=mini.getContext('2d');
function drawMini(){
  const Sz=mini.width,r=Sz/2,k=Sz/340*0.8;
  mg.save();mg.clearRect(0,0,Sz,Sz);mg.beginPath();mg.arc(r,r,r,0,Math.PI*2);mg.clip();
  mg.fillStyle='#93a96a';mg.fillRect(0,0,Sz,Sz);
  mg.translate(r,r);mg.rotate(car.th+Math.PI);
  for(const c of builtChunks())mg.drawImage(c.mini,(c.x0-car.x)*k,(c.z0-car.z)*k,CH*k,CH*k);
  mg.restore();
  mg.save();mg.translate(r,r);mg.fillStyle='#ff6a1a';mg.strokeStyle='#fff';mg.lineWidth=2;
  mg.beginPath();mg.moveTo(0,-11);mg.lineTo(8,9);mg.lineTo(0,5);mg.lineTo(-8,9);mg.closePath();mg.fill();mg.stroke();mg.restore();
}

/* ================= HUD ================= */
const hud=$('hud'),pauseEl=$('pause'),touchEl=$('touch'),picker=$('picker'),loadEl=$('loading');
const isTouch=matchMedia('(pointer:coarse)').matches;if(isTouch)document.body.classList.add('touch');
const H={score:$('hScore'),best:$('hBest'),drift:$('hDrift'),cur:$('hCur'),mult:$('hMult'),ang:$('hAng'),angBar:$('hAngBar'),spd:$('hSpd'),gear:$('hGear'),rpm:$('hRpm'),place:$('hPlace'),net:$('hNet')};
let placeT=0;
function updateHUD(dt,ang){
  H.score.textContent=score.toLocaleString('de-DE');
  H.best.textContent='Beste Combo '+bestCombo.toLocaleString('de-DE');
  H.drift.classList.toggle('on',cur>0);
  H.cur.textContent=Math.round(cur).toLocaleString('de-DE');
  H.mult.textContent='x'+mult;H.ang.textContent=Math.round(drifting?ang:0)+'°';
  H.angBar.style.width=(drifting?clamp(ang/60,0,1)*100:0)+'%';
  H.spd.textContent=Math.round(Math.hypot(car.vx,car.vz)*3.6);
  H.gear.textContent=car.gear<0?'R':car.gear;
  H.rpm.style.width=(car.rpm/8000*100)+'%';
  placeT-=dt;if(placeT<=0){placeT=.5;H.place.textContent=placeName(car.x,car.z)||(car.sf===3?'Wasser':'Gelände');
    const msg=W.error&&!W.busy?'Kartenserver antwortet nicht, neuer Versuch läuft':W.status;H.net.textContent=msg;H.net.hidden=!msg}
  if(toastT>0){toastT-=dt;if(toastT<.3)toastEl.style.opacity=Math.max(0,toastT/.3);if(toastT<=0)toastEl.hidden=true}
}

/* ================= flow ================= */
function placeCar(x,z,th){car.armed=false;car.vRate=0;car.x=x;car.z=z;car.th=th;car.vx=car.vz=car.w=0;car.steer=0;car.ax=car.ay=0}
let spawnAt=null;
function spawn(s){s=s||spawnAt;placeCar(s.x,s.z,s.th);const y=height(s.x,s.z);camPos.set(s.x-Math.sin(s.th)*8,y+3,s.z-Math.cos(s.th)*8);look.set(s.x,y+1,s.z)}
function resetToRoad(){
  const r=nearestRoad(car.x,car.z,250);
  if(r){const fwd=Math.atan2(r.dx,r.dz),alt=fwd+Math.PI,dd=a=>Math.abs(Math.atan2(Math.sin(a-car.th),Math.cos(a-car.th)));placeCar(r.x,r.z,dd(fwd)<dd(alt)?fwd:alt)}
  else placeCar(car.x,car.z,car.th);
  cur=0;mult=1;driftT=0;
}
function setPause(p){
  if(p&&state==='drive'){state='pause';pauseEl.hidden=false;touchEl.hidden=true;for(const k in keys)keys[k]=false}
  else if(!p&&state==='pause'){state='drive';pauseEl.hidden=true;touchEl.hidden=!isTouch}
}
function cycleCam(){camMode=(camMode+1)%4;toast(CAMS[camMode],'')}
function showPicker(){
  state='pick';unloadAll();clearSkids();
  hud.hidden=true;pauseEl.hidden=true;touchEl.hidden=true;loadEl.hidden=true;picker.hidden=false;
  setTimeout(()=>lmap&&lmap.invalidateSize(),50);
}
let loadTry=0;
async function go(){
  if(!selPt)return;
  initAudio();
  state='loading';picker.hidden=true;loadEl.hidden=false;$('loadErr').hidden=true;$('loadBtns').hidden=true;
  $('loadPlace').textContent=selPt.name||`${selPt.lat.toFixed(5)}, ${selPt.lon.toFixed(5)}`;
  const bar=$('loadBar'),step=$('loadStep');
  const my=++loadTry;
  setOrigin(selPt.lat,selPt.lon);
  try{
    await loadArea((t,p)=>{if(my!==loadTry)return;step.textContent=t;bar.style.width=Math.round(p*100)+'%'});
  }catch(e){
    if(my!==loadTry)return;
    $('loadErr').textContent='Die Kartendaten konnten nicht geladen werden ('+(e.message||'Netzwerkfehler')+'). Die Server sind manchmal kurz ausgelastet, ein zweiter Versuch klappt meistens.';
    $('loadErr').hidden=false;$('loadBtns').hidden=false;return;
  }
  if(my!==loadTry)return;
  spawnAt=spawnPoint();spawn(spawnAt);
  rememberPlace(selPt);
  try{history.replaceState(null,'','#'+selPt.lat.toFixed(5)+','+selPt.lon.toFixed(5))}catch(e){}
  loadEl.hidden=true;hud.hidden=false;touchEl.hidden=!isTouch;state='drive';score=0;cur=0;
  toast(spawnAt.name||selPt.name||'Los geht’s','good');
}
$('retryBtn').onclick=go;
$('backBtn').onclick=showPicker;
$('resumeBtn').onclick=()=>setPause(false);
$('newPlaceBtn').onclick=showPicker;
$('respawnBtn').onclick=()=>{spawn(spawnAt);setPause(false)};
$('pauseBtn').onclick=()=>setPause(true);$('camBtn').onclick=cycleCam;
$('sndBtn').onclick=()=>{muted=!muted;$('sndBtn').classList.toggle('off',muted)};
const syncAssist=v=>{assist=v;$('assist').checked=v;$('assist2').checked=v;store.set('driftline-assist',v)};
$('assist').onchange=e=>syncAssist(e.target.checked);$('assist2').onchange=e=>syncAssist(e.target.checked);
syncAssist(store.get('driftline-assist',true));

/* ================= garage ================= */
function buildGarage(){
  const wrap=$('cars');wrap.innerHTML='';
  PRESETS.forEach((p,i)=>{
    const b=document.createElement('button');b.className='car';b.type='button';b.setAttribute('aria-pressed',i===sel);
    b.innerHTML=`<b>${p.name}</b><span>${Math.round(p.power/1000*1.36)} PS · ${p.mass} kg</span>`;
    b.onclick=()=>{sel=i;store.set('driftline-car',i);buildCar();[...wrap.children].forEach((el,k)=>el.setAttribute('aria-pressed',k===i))};
    wrap.append(b);
  });
  const pw=$('paint');pw.innerHTML='';
  PAINTS.forEach((c,i)=>{const s=document.createElement('button');s.type='button';s.className='sw';s.style.background=c;s.setAttribute('aria-label','Lackfarbe '+(i+1));s.setAttribute('aria-pressed',i===paint);
    s.onclick=()=>{paint=i;store.set('driftline-paint',i);paintMat.color.set(c);pw.querySelectorAll('.sw').forEach((el,k)=>el.setAttribute('aria-pressed',k===i))};pw.append(s)});
}
sel=clamp(store.get('driftline-car',1)|0,0,PRESETS.length-1);paint=clamp(store.get('driftline-paint',1)|0,0,PAINTS.length-1);

/* ================= map picker ================= */
let lmap=null,marker=null,area=null,selPt=null,satOn=false,osmL=null,satL=null;
function initPicker(){
  if(!window.L){$('pickErr').textContent='Die Karte konnte nicht geladen werden. Prüfe deine Internetverbindung und lade die Seite neu.';$('pickErr').hidden=false;return}
  const last=store.get('driftline-recent',[])[0];
  lmap=L.map('map',{zoomControl:false,attributionControl:true,worldCopyJump:true}).setView(last?[last.lat,last.lon]:[51.1,10.4],last?15:6);
  L.control.zoom({position:'topright'}).addTo(lmap);
  osmL=L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png',{maxZoom:19,attribution:'© <a href="https://www.openstreetmap.org/copyright" target="_blank" rel="noopener">OpenStreetMap</a>-Mitwirkende'}).addTo(lmap);
  satL=L.tileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}',{maxZoom:19,attribution:'Luftbild © Esri, Maxar, Earthstar Geographics'});
  lmap.on('click',e=>choose(e.latlng.lat,e.latlng.lng));
  const h=location.hash.match(/^#(-?\d+(?:\.\d+)?),(-?\d+(?:\.\d+)?)$/);
  if(h){const la=+h[1],lo=+h[2];if(Math.abs(la)<85&&Math.abs(lo)<=180){lmap.setView([la,lo],16);choose(la,lo)}}
  renderRecent();
}
const pinIcon=()=>L.divIcon({className:'pin',html:'<span></span>',iconSize:[26,26],iconAnchor:[13,13]});
async function choose(lat,lon,name){
  selPt={lat,lon,name:name||null};
  if(!marker)marker=L.marker([lat,lon],{icon:pinIcon()}).addTo(lmap);else marker.setLatLng([lat,lon]);
  const dLat=CH*1.5/110574,dLon=CH*1.5/(111320*Math.cos(lat*Math.PI/180));
  const bounds=[[lat-dLat,lon-dLon],[lat+dLat,lon+dLon]];
  if(!area)area=L.rectangle(bounds,{color:'#ff6a1a',weight:2,fillOpacity:.06,dashArray:'6 6',interactive:false}).addTo(lmap);else area.setBounds(bounds);
  $('selName').textContent=name||'Ort wird gesucht …';$('selCoord').textContent=`${lat.toFixed(5)}, ${lon.toFixed(5)}`;
  $('goBtn').disabled=false;
  if(!name){const r=await reverse(lat,lon);if(selPt&&selPt.lat===lat&&selPt.lon===lon){selPt.name=shortName(r)||null;$('selName').textContent=selPt.name||'Unbenannter Ort'}}
}
function rememberPlace(p){
  let list=store.get('driftline-recent',[]).filter(x=>Math.abs(x.lat-p.lat)>1e-4||Math.abs(x.lon-p.lon)>1e-4);
  list.unshift({lat:+p.lat.toFixed(6),lon:+p.lon.toFixed(6),name:p.name||null});store.set('driftline-recent',list.slice(0,6));renderRecent();
}
function renderRecent(){
  const list=store.get('driftline-recent',[]),w=$('recent');w.innerHTML='';$('recentWrap').hidden=!list.length;
  list.forEach(p=>{const b=document.createElement('button');b.type='button';b.className='chip';b.textContent=p.name||`${p.lat.toFixed(4)}, ${p.lon.toFixed(4)}`;b.onclick=()=>{lmap.setView([p.lat,p.lon],16);choose(p.lat,p.lon,p.name)};w.append(b)});
}
$('searchForm').addEventListener('submit',async e=>{
  e.preventDefault();const q=$('q').value.trim();if(!q)return;
  const ul=$('results');ul.innerHTML='<li class="muted">Suche …</li>';
  try{const res=await search(q);ul.innerHTML='';
    if(!res.length){ul.innerHTML='<li class="muted">Nichts gefunden. Versuch es mit Straße und Ort.</li>';return}
    res.forEach(r=>{const li=document.createElement('li');const b=document.createElement('button');b.type='button';b.textContent=r.display_name;
      b.onclick=()=>{ul.innerHTML='';const la=+r.lat,lo=+r.lon;lmap.setView([la,lo],16);choose(la,lo,shortName(r))};li.append(b);ul.append(li)});
  }catch(err){ul.innerHTML='<li class="muted">Die Suche ist gerade nicht erreichbar. Tippe den Ort direkt auf der Karte an.</li>'}
});
$('locBtn').onclick=()=>{
  if(!navigator.geolocation){toastPick('Standort wird von diesem Browser nicht unterstützt.');return}
  $('locBtn').textContent='Suche Standort …';
  navigator.geolocation.getCurrentPosition(p=>{$('locBtn').textContent='Mein Standort';const la=p.coords.latitude,lo=p.coords.longitude;lmap.setView([la,lo],16);choose(la,lo)},
    ()=>{$('locBtn').textContent='Mein Standort';toastPick('Standort nicht verfügbar. Erlaube den Zugriff oder tippe auf die Karte.')},{enableHighAccuracy:true,timeout:10000});
};
$('layerBtn').onclick=()=>{satOn=!satOn;if(satOn){lmap.removeLayer(osmL);satL.addTo(lmap)}else{lmap.removeLayer(satL);osmL.addTo(lmap)}$('layerBtn').textContent=satOn?'Karte':'Satellit'};
$('goBtn').onclick=go;
function toastPick(t){const e=$('pickErr');e.textContent=t;e.hidden=false;clearTimeout(toastPick.t);toastPick.t=setTimeout(()=>e.hidden=true,4000)}

/* ================= loop ================= */
function resize(){const w=innerWidth,h=innerHeight;renderer.setSize(w,h,false);camera.aspect=w/h;camera.updateProjectionMatrix()}
addEventListener('resize',resize);
let last=performance.now(),acc=0,ang=0;
function frame(now){
  requestAnimationFrame(frame);
  const dt=Math.min(.1,(now-last)/1000);last=now;
  if(state==='pick'||state==='loading'){updateAudio();return}
  if(state==='drive'){
    readInput(dt);acc+=dt;const h=1/120;
    while(acc>=h){physics(h);collide();acc-=h}
    ang=updateScore(dt);effects(dt);
  }else acc=0;
  updateWorld(car.x,car.z,dt);
  updateSmoke(dt);
  syncCar(dt);updateCamera(dt,now/1000);
  smokeMat.uniforms.uScale.value=innerHeight*DPR/(2*Math.tan(camera.fov*Math.PI/360));
  renderer.render(scene,camera);
  updateHUD(dt,ang);drawMini();
  updateAudio();
}
buildCar();buildGarage();resize();initPicker();
if(/[?&]debug/.test(location.search))window.__dl={car,tp:(x,z,th)=>{placeCar(x,z,th||0);camPos.set(x,height(x,z)+3,z-8)},W};
requestAnimationFrame(t=>{last=t;frame(t)});
