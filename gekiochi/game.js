'use strict';
const $=id=>document.getElementById(id);

// ================= 定数 =================
// 机2台をくっつけた盤面（教室あるあるで、ちょっとズレてる）
const DESKS=[{x0:-20,x1:0,z0:-6,z1:7},{x0:0,x1:20,z0:-7,z1:6}];
const W=20, D=7;                // 盤面全体のおおよその半分サイズ
const START_X=12;
const EL=1.8, EH=0.7, EW=1.0;   // 消しゴム
const R=0.62;                   // 当たり判定半径
const PR=0.22, PH=0.44;         // 鉛筆半径・高さ
const RUL_HW=0.42, RUL_H=0.18;   // 定規の半幅・厚み
const GRAV=30, MU=9, CA=11, FLOOR=-25, DT=1/120;
const TYPE_NAMES=['ストレート','ループ','カーブ'];
const PEER_PFX='gekiochi-keshigomu-v3-';
// 消しゴムの種類
const ETYPES=[
  {name:'ふつうの消しゴム',rr:0.07,short:'ふつう',label:'激落',desc:'普通のステータスだぞ。',stats:[3,3,3,3],
   spd:1.0,mu:9,m:1.0,rest:0.85,oRest:0.45,land:0.22,squish:0.45,body:0xf7f6f0,rough:0.95,metal:0},
  {name:'ツルツル消しゴム',rr:0.11,clear:1,short:'ツルツル',label:'ツルツル',desc:'めっちゃ滑る。当てた相手もツルッと滑らせる！ ぶつけられると止まらないのが弱点。',stats:[5,5,2,2],
   spd:1.15,mu:6.2,m:0.9,rest:0.7,oRest:0.35,land:0.15,squish:0.25,body:0x7fd2ff,rough:0.12,metal:0.15},
  {name:'もちもち消しゴム',rr:0.26,jelly:1,short:'もちもち',label:'もちもち',desc:'弾力がすごい。当たった相手をボヨーンと弾き飛ばす。足はおそい。',stats:[2,1,5,4],
   spd:0.9,mu:11,m:1.15,rest:1.3,oRest:0.95,land:0.6,squish:1.0,body:0xff9cc0,rough:0.8,metal:0},
  // ボス専用（プレイヤーは選べない）。ふつうより少し重い
  {name:'おうごん消しゴム',rr:0.06,short:'おうごん',label:'王者',desc:'激落王だけが持つ伝説の消しゴム。',stats:[3,3,3,4],
   spd:1.0,mu:9,m:1.12,rest:0.85,oRest:0.45,land:0.22,squish:0.4,body:0xffc928,rough:0.35,metal:0,emis:0x8a5a00,sleeve:'#1b1430'},
  {name:'ちびちび消しゴム',rr:0.16,worn:1,short:'ちびちび',label:'ちびちび',desc:'使い古しで小さい。当たりにくくて足が速い。でも軽いから当たると吹っ飛ぶ。',stats:[5,3,2,1],
   spd:1.25,mu:8.5,m:0.8,rest:1.0,oRest:0.5,land:0.3,squish:0.4,body:0xe8e2d2,rough:0.95,metal:0,sz:0.7},
  {name:'ブッとび消しゴム',rr:0.3,stripe:1,short:'ブッとび',label:'ブッとび',desc:'ぶつかると3回に1回、相手を空中にブッとばす！ 軽いので自分も飛ばされやすい。',stats:[4,3,4,2],
   spd:1.1,mu:9,m:0.85,rest:0.95,oRest:0.55,land:0.4,squish:0.5,body:0xff9a3c,rough:0.7,metal:0,pop:1},
];
// プレイヤーが選べる消しゴム（3番はボス専用）
const PLAYABLE=[0,1,2,4,5],randType=()=>PLAYABLE[(Math.random()*PLAYABLE.length)|0];
// 勝ち抜き戦で解放したもの（端末に保存）
const UNL=new Set();try{(JSON.parse(SAVE.getItem('gekiochiUnlock')||'[]')||[]).forEach(x=>UNL.add(String(x)))}catch(e){}
function unlock(id){if(UNL.has(id))return false;UNL.add(id);try{SAVE.setItem('gekiochiUnlock',JSON.stringify([...UNL]))}catch(e){}return true}
const goldOpen=()=>UNL.has('e3');
const STAT_NAMES=['スピード','すべり','弾力','重さ'];

function mulberry32(a){return function(){a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296}}
const clamp=(v,a,b)=>Math.max(a,Math.min(b,v));
function angDiff(a,b){let d=b-a;while(d>Math.PI)d-=2*Math.PI;while(d<-Math.PI)d+=2*Math.PI;return d}
function gauss(){return (Math.random()+Math.random()+Math.random()-1.5)/0.5}

// ================= 物理 =================
function closestPt(ax,az,bx,bz,x,z){const dx=bx-ax,dz=bz-az;const t=clamp(((x-ax)*dx+(z-az)*dz)/(dx*dx+dz*dz),0,1);return[ax+dx*t,az+dz*t]}
// 線分同士の最近接点（Ericson）
function segSeg(p1x,p1z,q1x,q1z,p2x,p2z,q2x,q2z){
  const d1x=q1x-p1x,d1z=q1z-p1z,d2x=q2x-p2x,d2z=q2z-p2z,rx=p1x-p2x,rz=p1z-p2z;
  const a=d1x*d1x+d1z*d1z,e=d2x*d2x+d2z*d2z,f=d2x*rx+d2z*rz,c=d1x*rx+d1z*rz,b=d1x*d2x+d1z*d2z,den=a*e-b*b;
  let s=den>1e-9?clamp((b*f-c*e)/den,0,1):0,t=(b*s+f)/e;
  if(t<0){t=0;s=clamp(-c/a,0,1)}else if(t>1){t=1;s=clamp((b-c)/a,0,1)}
  return[p1x+d1x*s,p1z+d1z*s,p2x+d2x*t,p2z+d2z*t];
}
function obsEnds(o){const hx=Math.cos(o.a)*o.L,hz=Math.sin(o.a)*o.L;return[o.cx-hx,o.cz-hz,o.cx+hx,o.cz+hz]}
function obsDist(A,B){const a=obsEnds(A),b=obsEnds(B),c=segSeg(...a,...b);return Math.hypot(c[2]-c[0],c[3]-c[1])}
// 障害物：kind 0=鉛筆 1=定規（どちらも「線分＋半径」のカプセルとして扱う）
function mkObs(kind,cx,cz,a,len,col){
  const pen=kind===0,m=pen?0.45:1.4;
  return{kind,cx,cz,a,len,L:len/2,r:pen?PR:RUL_HW,h:pen?PH:RUL_H,m,I:m*len*len/12,vx:0,vz:0,w:0,falling:false,y:0,vy:0,tilt:0,wt:0,roll:0,col};
}
function makeObstacles(seed){
  const rnd=mulberry32(seed>>>0),os=[];
  const tryPlace=(kind,lenF,cxR,czR,n)=>{let tries=0,placed=0;
    while(placed<n&&tries<500){tries++;
      const o=mkObs(kind,(rnd()*2-1)*cxR,(rnd()*2-1)*czR,rnd()*Math.PI,lenF(),(rnd()*3)|0);
      const [ax,az,bx,bz]=obsEnds(o),mg=o.r+0.5;
      if(!inTable(ax,az,mg)||!inTable(bx,bz,mg)||!inTable(o.cx,o.cz,mg))continue;
      let ok=true;for(const sx of[-START_X,START_X]){const c=closestPt(ax,az,bx,bz,sx,0);if(Math.hypot(sx-c[0],c[1])<R+o.r+1.3)ok=false}
      if(!ok||os.some(q=>obsDist(o,q)<o.r+q.r+0.9))continue;
      os.push(o);placed++;
    }};
  tryPlace(1,()=>7+rnd()*1.6,W-4.5,D-3.1,2);   // 定規 2本
  tryPlace(0,()=>4.5+rnd()*2.8,W-2.5,D-2.1,6);  // 鉛筆 6本
  return os;
}
function mkE(x,z,yaw,k=0){const T=ETYPES[k];return{x,y:0,z,vx:0,vy:0,vz:0,yaw,w:0,curve:0,falling:false,fell:false,rx:0,rz:0,wr:0,sz:T.sz||1,r:R*(T.sz||1),
  k,spd:T.spd,mu:T.mu,m:T.m,rest:T.rest,oRest:T.oRest,land:T.land}}
function newState(seed,types=[0,0]){return{e:[mkE(-START_X,0,0,types[0]),mkE(START_X,0,Math.PI,types[1])],obs:makeObstacles(seed),t:0}}
function cloneState(s){return{e:s.e.map(o=>Object.assign({},o)),obs:s.obs.map(o=>Object.assign({},o)),t:s.t}}
function in0(x,z){for(const d of DESKS)if(x>=d.x0&&x<=d.x1&&z>=d.z0&&z<=d.z1)return true;return false}
// m>0 のときは「縁から m 以上内側か」（つなぎ目は内側扱い）
function edgeDist(e){const D=DESKS[e.x<0?0:1];return Math.min(20-Math.abs(e.x),e.z-D.z0,D.z1-e.z)}
function inTable(x,z,m=0){return in0(x,z)&&(m===0||(in0(x+m,z+m)&&in0(x-m,z+m)&&in0(x+m,z-m)&&in0(x-m,z-m)))}
const onTable=e=>inTable(e.x,e.z);
// 一番近い机の上の点（落ちる方向を決めるため）
function nearestOnTable(x,z){let best=null,bd=1e9;for(const d of DESKS){const cx=clamp(x,d.x0,d.x1),cz=clamp(z,d.z0,d.z1),dd=Math.hypot(x-cx,z-cz);if(dd<bd){bd=dd;best=[cx,cz]}}return best}

function launch(s,i,sh){
  const e=s.e[i],v=(3+17*sh.power)*e.spd;let a=sh.angle,hv=v;e.curve=0;e.w=0;
  if(sh.type===1){hv=v*0.78;e.vy=6+4.5*sh.power;e.y=0.001}
  if(sh.type===2){a-=sh.curve*0.32;e.curve=sh.curve;e.w=sh.curve*9;hv=v*1.05}
  e.vx=Math.cos(a)*hv;e.vz=Math.sin(a)*hv;e.yaw=sh.angle;
}
function startFall(e,ev,i){
  e.falling=true;e.fell=true;e.curve=0;
  const c=nearestOnTable(e.x,e.z);let ox=e.x-c[0],oz=e.z-c[1];const ol=Math.hypot(ox,oz);
  if(ol>1e-6){e.vx+=ox/ol*1.2;e.vz+=oz/ol*1.2}
  e.wr=4+Math.hypot(e.vx,e.vz)*0.5;
  ev&&ev.push({k:'fall',i,x:e.x,z:e.z});
}
const BUTTOBI_P=1/3;
function luck(a,b,t){const v=Math.sin(a.x*12.9898+a.z*4.1414+b.x*78.233+b.z*39.425+t*137.31)*43758.5453;return v-Math.floor(v)}
function step(s,dt,ev){
  s.t+=dt;
  for(let i=0;i<2;i++){const e=s.e[i];
    if(e.falling){
      if(e.y>FLOOR){e.vy-=GRAV*dt;e.x+=e.vx*dt;e.y+=e.vy*dt;e.z+=e.vz*dt;e.rx+=e.wr*dt;e.rz+=e.wr*0.7*dt;e.yaw+=e.w*dt;
        if(e.y<=FLOOR){e.y=FLOOR;e.vx=e.vy=e.vz=0;e.wr=0;e.w=0;e.rx=Math.round(e.rx/(Math.PI/2))*(Math.PI/2);e.rz=Math.round(e.rz/(Math.PI/2))*(Math.PI/2);ev&&ev.push({k:'floor',i})}}
      continue;
    }
    if(e.y>0||e.vy>0){
      e.vy-=GRAV*dt;e.x+=e.vx*dt;e.z+=e.vz*dt;e.y+=e.vy*dt;
      if(e.y<=0){
        if(onTable(e)){const iv=e.vy;e.y=0;e.vy=iv<-4?-iv*e.land:0;e.vx*=0.85;e.vz*=0.85;ev&&ev.push({k:'land',i,p:-iv,x:e.x,z:e.z})}
        else{e.y=0;startFall(e,ev,i)}
      }
    }else{
      let sp=Math.hypot(e.vx,e.vz);
      if(sp>0){
        if(e.curve&&sp>0.4){const k=CA*Math.min(1,sp/5)*dt*e.curve;const nx=-e.vz/sp,nz=e.vx/sp;e.vx+=nx*k;e.vz+=nz*k;const ns=Math.hypot(e.vx,e.vz);e.vx*=sp/ns;e.vz*=sp/ns}
        const ns=Math.max(0,sp-e.mu*(e.slick?0.5:1)*dt);
        if(ns===0){e.vx=e.vz=0;e.curve=0;e.slick=0}else{e.vx*=ns/sp;e.vz*=ns/sp}
        e.x+=e.vx*dt;e.z+=e.vz*dt;
      }
      if(!onTable(e))startFall(e,ev,i);
    }
    e.yaw+=e.w*dt;e.w*=Math.max(0,1-(e.y>0?0.4:2.6)*dt);
  }
  // 障害物の移動（鉛筆は軸の向きに転がりやすい）
  for(const o of s.obs){
    if(o.falling){
      if(o.y>FLOOR){o.vy-=GRAV*dt;o.cx+=o.vx*dt;o.cz+=o.vz*dt;o.y+=o.vy*dt;o.a+=o.w*dt;o.tilt+=o.wt*dt;
        if(o.y<=FLOOR){o.y=FLOOR;o.vx=o.vz=o.vy=0;o.w=0;o.wt=0;o.tilt=Math.round(o.tilt/Math.PI)*Math.PI;ev&&ev.push({k:'ofloor',kind:o.kind})}}
      continue;
    }
    if(o.vx!==0||o.vz!==0){
      const c=Math.cos(o.a),sn=Math.sin(o.a);let va=o.vx*c+o.vz*sn,vp=-o.vx*sn+o.vz*c;
      const fa=(o.kind===0?6.5:6)*dt,fp=(o.kind===0?2.2:6)*dt;
      va=Math.sign(va)*Math.max(0,Math.abs(va)-fa);vp=Math.sign(vp)*Math.max(0,Math.abs(vp)-fp);
      o.vx=va*c-vp*sn;o.vz=va*sn+vp*c;if(o.kind===0)o.roll+=vp*dt/o.r;
      o.cx+=o.vx*dt;o.cz+=o.vz*dt;
    }
    if(o.w!==0){o.w=Math.sign(o.w)*Math.max(0,Math.abs(o.w)-(o.kind===0?4:3)*dt);o.w*=(1-0.6*dt);if(Math.abs(o.w)<0.02)o.w=0;o.a+=o.w*dt}
    if(!inTable(o.cx,o.cz)){o.falling=true;o.vy=0;const sp=Math.hypot(o.vx,o.vz);o.wt=(o.kind===0?5:3)+sp*0.4;
      const c=nearestOnTable(o.cx,o.cz),ox=o.cx-c[0],oz=o.cz-c[1],ol=Math.hypot(ox,oz);if(ol>1e-6){o.vx+=ox/ol;o.vz+=oz/ol}
      ev&&ev.push({k:'ofall',kind:o.kind,x:o.cx,z:o.cz})}
  }
  // 消しゴム同士
  const a=s.e[0],b=s.e[1];
  if(!a.falling&&!b.falling&&Math.abs(a.y-b.y)<EH){
    let dx=b.x-a.x,dz=b.z-a.z,d=Math.hypot(dx,dz);
    if(d<a.r+b.r){
      if(d<1e-6){dx=1;dz=0;d=1}
      const nx=dx/d,nz=dz/d,ov=a.r+b.r-d,ia=1/a.m,ib=1/b.m;
      a.x-=nx*ov*ia/(ia+ib);a.z-=nz*ov*ia/(ia+ib);b.x+=nx*ov*ib/(ia+ib);b.z+=nz*ov*ib/(ia+ib);
      const rv=(b.vx-a.vx)*nx+(b.vz-a.vz)*nz;
      if(rv<0){
        const j=-(1+(a.rest+b.rest)/2)*rv/(ia+ib);
        a.vx-=j*nx*ia;a.vz-=j*nz*ia;b.vx+=j*nx*ib;b.vz+=j*nz*ib;
        const tx=-nz,tz=nx,rt=(b.vx-a.vx)*tx+(b.vz-a.vz)*tz;
        a.w-=rt*1.2+(-rv)*0.4;b.w+=rt*1.2+(-rv)*0.5;a.curve=b.curve=0;
        let sl=false,bu=false;
        if(-rv>2){if(a.k===1){b.slick=1;sl=true}if(b.k===1){a.slick=1;sl=true}
          // ブッとびは確率技（3回に1回）。通信対戦でも両方で同じ結果になるよう、盤面から決まる乱数を使う。予測線とCPUの読みには入れない
          if((a.k===5||b.k===5)&&!s.noLuck&&luck(a,b,s.t)<BUTTOBI_P){if(a.k===5){b.vy=Math.max(b.vy,Math.min(9,-rv*0.55));bu=true}if(b.k===5){a.vy=Math.max(a.vy,Math.min(9,-rv*0.55));bu=true}}}
        ev&&ev.push({k:'hit',vic:Math.hypot(a.vx,a.vz)>=Math.hypot(b.vx,b.vz)?0:1,p:-rv,x:(a.x+b.x)/2,y:(a.y+b.y)/2,z:(a.z+b.z)/2,mochi:(a.k===2||b.k===2),slick:sl,buttobi:bu});
      }
    }
  }
  // 消しゴム × 鉛筆・定規（剛体として押し合う）
  for(let i=0;i<2;i++){const e=s.e[i];if(e.falling)continue;
    for(const o of s.obs){if(o.falling||e.y>=o.h)continue;
      const [ax,az,bx,bz]=obsEnds(o),[px,pz]=closestPt(ax,az,bx,bz,e.x,e.z);
      let dx=e.x-px,dz=e.z-pz,d=Math.hypot(dx,dz);const rr=e.r+o.r;
      if(d>=rr)continue;
      let nx,nz;if(d<1e-6){nx=-Math.sin(o.a);nz=Math.cos(o.a);d=0}else{nx=dx/d;nz=dz/d}
      const ie=1/e.m,io=1/o.m,ov=rr-d;
      e.x+=nx*ov*ie/(ie+io);e.z+=nz*ov*ie/(ie+io);o.cx-=nx*ov*io/(ie+io);o.cz-=nz*ov*io/(ie+io);
      const rx=px+nx*o.r-o.cx,rz=pz+nz*o.r-o.cz;
      const vrel=(e.vx-(o.vx-o.w*rz))*nx+(e.vz-(o.vz+o.w*rx))*nz;
      if(vrel<0){
        const rn=rx*nz-rz*nx,j=-(1+e.oRest)*vrel/(ie+io+rn*rn/o.I);
        e.vx+=j*nx*ie;e.vz+=j*nz*ie;o.vx-=j*nx*io;o.vz-=j*nz*io;o.w-=j*rn/o.I;
        e.curve=0;e.w+=vrel*0.5;
        ev&&ev.push({k:'obs',i,kind:o.kind,p:-vrel,x:px,z:pz});
      }
    }
  }
  // 障害物同士
  const O=s.obs;
  for(let p=0;p<O.length;p++)for(let q=p+1;q<O.length;q++){
    const A=O[p],B=O[q];if(A.falling||B.falling)continue;
    if(A.vx===0&&A.vz===0&&A.w===0&&B.vx===0&&B.vz===0&&B.w===0)continue;
    if(Math.hypot(A.cx-B.cx,A.cz-B.cz)>A.L+B.L+A.r+B.r)continue;
    const c=segSeg(...obsEnds(A),...obsEnds(B));
    let dx=c[2]-c[0],dz=c[3]-c[1],d=Math.hypot(dx,dz);const rr=A.r+B.r;
    if(d>=rr)continue;
    let nx,nz;if(d<1e-6){nx=-Math.sin(A.a);nz=Math.cos(A.a);d=0}else{nx=dx/d;nz=dz/d}
    const ia=1/A.m,ib=1/B.m,ov=rr-d;
    A.cx-=nx*ov*ia/(ia+ib);A.cz-=nz*ov*ia/(ia+ib);B.cx+=nx*ov*ib/(ia+ib);B.cz+=nz*ov*ib/(ia+ib);
    const cx=c[0]+nx*A.r,cz=c[1]+nz*A.r,rax=cx-A.cx,raz=cz-A.cz,rbx=cx-B.cx,rbz=cz-B.cz;
    const vrel=((B.vx-B.w*rbz)-(A.vx-A.w*raz))*nx+((B.vz+B.w*rbx)-(A.vz+A.w*rax))*nz;
    if(vrel<0){
      const ran=rax*nz-raz*nx,rbn=rbx*nz-rbz*nx,j=-(1+0.4)*vrel/(ia+ib+ran*ran/A.I+rbn*rbn/B.I);
      A.vx-=j*nx*ia;A.vz-=j*nz*ia;A.w-=j*ran/A.I;B.vx+=j*nx*ib;B.vz+=j*nz*ib;B.w+=j*rbn/B.I;
      ev&&ev.push({k:'oo',p:-vrel,x:cx,z:cz});
    }
  }
}
const isStill=e=>e.y===0&&e.vy===0&&e.vx===0&&e.vz===0;
const oStill=o=>o.vx===0&&o.vz===0&&o.w===0;
function settled(s){return s.e.every(e=>e.falling?e.y<=FLOOR:isStill(e))&&s.obs.every(o=>o.falling?o.y<=FLOOR:oStill(o))}
function quiet(s){return s.e.every(e=>e.falling||isStill(e))&&s.obs.every(o=>o.falling||oStill(o))}
function serState(s){return{e:s.e.map(e=>[e.x,e.y,e.z,e.yaw,e.falling?1:0,e.fell?1:0,e.rx,e.rz]),o:s.obs.map(o=>[o.cx,o.cz,o.a,o.falling?1:0,o.y,o.tilt,o.roll])}}
function applyState(s,st){
  st.e.forEach((a,i)=>{const e=s.e[i];[e.x,e.y,e.z,e.yaw]=a;e.falling=!!a[4];e.fell=!!a[5];e.rx=a[6];e.rz=a[7];e.vx=e.vy=e.vz=0;e.w=0;e.wr=0;e.curve=0});
  st.o.forEach((a,i)=>{const o=s.obs[i];if(!o)return;[o.cx,o.cz,o.a]=a;o.falling=!!a[3];o.y=a[4];o.tilt=a[5];o.roll=a[6];o.vx=o.vz=o.vy=0;o.w=0;o.wt=0});
}

// ================= CPU =================
const DIR8=[...Array(12)].map((_,k)=>[Math.cos(k*Math.PI/6),Math.sin(k*Math.PI/6)]);
function edgeDist(e){let m=6;for(const[dx,dz]of DIR8)for(let r=0.3;r<m;r+=0.3)if(!inTable(e.x+dx*r,e.z+dz*r)){m=r;break}return m}
function evalShot(s0,i,sh){
  const s=cloneState(s0);s.noLuck=true;launch(s,i,sh);
  for(let k=0;k<800;k++){step(s,DT*2,null);if(k%8===7&&quiet(s))break}
  const me=s.e[i],op=s.e[1-i];let sc=0;
  if(me.fell)sc-=1000;
  if(op.fell)sc+=600;else sc+=(6-edgeDist(op))*8;
  if(!me.fell){const ed=edgeDist(me);sc+=Math.min(ed,3)*6;if(ed<1.3)sc-=(1.3-ed)*40}
  return sc;
}
function cpuChoose(s,i,diff){
  const cfg=typeof diff==='object'?diff:[{n:40,na:0.2,np:0.16},{n:140,na:0.06,np:0.06},{n:360,na:0.012,np:0.015}][diff];
  const me=s.e[i],op=s.e[1-i],base=Math.atan2(op.z-me.z,op.x-me.x),r=Math.random;
  if(cfg.easy){let best=null,bs=-1e9;
    for(let k=0;k<cfg.n;k++){const sh={type:0,curve:1,angle:r()*Math.PI*2,power:0.12+r()*0.3},t=cloneState(s);launch(t,i,sh);
      for(let j=0;j<500;j++){step(t,DT*2,null);if(j%8===7&&quiet(t))break}
      const a=t.e[i],b=t.e[1-i];let sc=-Math.abs(edgeDist(a)-1.1)*10+r()*3;
      if(a.fell)sc-=1000;if(Math.hypot(b.x-op.x,b.z-op.z)>0.05||b.fell)sc-=800;if(sc>bs){bs=sc;best=sh}}
    return best}
  let best=null,bs=-1e9;
  for(let k=0;k<cfg.n;k++){
    const sh={type:(r()*3)|0,curve:r()<0.5?-1:1,angle:r()<0.8?base+(r()*2-1)*0.75:r()*Math.PI*2,power:0.15+r()*0.85};
    const sc=evalShot(s,i,sh)+r()*4;if(sc>bs){bs=sc;best=sh}
  }
  if(diff===2||cfg.refine)for(let k=0;k<100;k++){
    const sh=Object.assign({},best,{angle:best.angle+(r()*2-1)*0.08,power:clamp(best.power+(r()*2-1)*0.08,0.1,1)});
    const sc=evalShot(s,i,sh);if(sc>bs){bs=sc;best=sh}
  }
  const out=Object.assign({},best);out.angle+=gauss()*cfg.na;out.power=clamp(out.power+gauss()*cfg.np,0.08,1);
  return out;
}

// ================= サウンド =================
let AC=null,muted=false,noiseBuf=null,SEOUT=null;
// 音量（0〜1）。BGMと効果音は別々に調整できる
const VOL={bgm:1,se:1};try{const v=JSON.parse(SAVE.getItem('gekiochiVol')||'null');if(v){VOL.bgm=clamp(+v.bgm||0,0,1);VOL.se=clamp(+v.se||0,0,1)}else if(SAVE.getItem('gekiochiBgm')==='0')VOL.bgm=0}catch(e){}
muted=VOL.se===0;
function seOut(a){if(!SEOUT){SEOUT=a.createGain();SEOUT.connect(a.destination)}SEOUT.gain.value=VOL.se;return SEOUT}
function ac(){
  if(!AC){try{AC=new(window.AudioContext||window.webkitAudioContext)();const n=AC.sampleRate;noiseBuf=AC.createBuffer(1,n,AC.sampleRate);const d=noiseBuf.getChannelData(0);for(let i=0;i<n;i++)d[i]=Math.random()*2-1}catch(e){}}
  if(AC&&AC.state==='suspended')AC.resume();if(AC&&!BGM.gain)bgmEnsure();return AC;
}
function noise(dur,freq,type,vol,t0=0){const a=ac();if(!a||muted)return;const t=a.currentTime+t0;const src=a.createBufferSource();src.buffer=noiseBuf;const f=a.createBiquadFilter();f.type=type;f.frequency.value=freq;const g=a.createGain();g.gain.setValueAtTime(vol,t);g.gain.exponentialRampToValueAtTime(0.001,t+dur);src.connect(f).connect(g).connect(seOut(a));src.start(t);src.stop(t+dur+0.02)}
function tone(f1,f2,dur,type,vol,t0=0){const a=ac();if(!a||muted)return;const t=a.currentTime+t0;const o=a.createOscillator();o.type=type;o.frequency.setValueAtTime(f1,t);o.frequency.exponentialRampToValueAtTime(f2,t+dur);const g=a.createGain();g.gain.setValueAtTime(vol,t);g.gain.exponentialRampToValueAtTime(0.001,t+dur);o.connect(g).connect(seOut(a));o.start(t);o.stop(t+dur+0.02)}
function sweep(dur,f1,f2,q,vol,t0=0){const a=ac();if(!a||muted)return;const t=a.currentTime+t0;const src=a.createBufferSource();src.buffer=noiseBuf;src.loop=true;const f=a.createBiquadFilter();f.type='bandpass';f.Q.value=q;f.frequency.setValueAtTime(f1,t);f.frequency.exponentialRampToValueAtTime(f2,t+dur);const g=a.createGain();g.gain.setValueAtTime(0.001,t);g.gain.exponentialRampToValueAtTime(vol,t+dur*0.25);g.gain.exponentialRampToValueAtTime(0.001,t+dur);src.connect(f).connect(g).connect(seOut(a));src.start(t);src.stop(t+dur+0.02)}
// パワーチャージ音（ゲージに合わせて音程が上下）
const charge={o:null,g:null,lfo:null};
function chargeStart(){const a=ac();if(!a||muted||charge.o)return;const o=a.createOscillator(),g=a.createGain(),l=a.createOscillator(),lg=a.createGain();o.type='sawtooth';l.frequency.value=18;lg.gain.value=0.025;l.connect(lg).connect(g.gain);g.gain.value=0.04;const f=a.createBiquadFilter();f.type='lowpass';f.frequency.value=1800;o.connect(f).connect(g).connect(seOut(a));o.start();l.start();Object.assign(charge,{o,g,lfo:l})}
function chargeSet(p){if(!charge.o)return;const t=AC.currentTime;charge.o.frequency.setTargetAtTime(110+p*620,t,0.02);charge.g.gain.setTargetAtTime(0.03+p*0.05,t,0.03);charge.lfo.frequency.setTargetAtTime(10+p*30,t,0.05)}
function chargeStop(){if(!charge.o)return;try{const t=AC.currentTime;charge.g.gain.setTargetAtTime(0,t,0.02);charge.o.stop(t+0.1);charge.lfo.stop(t+0.1)}catch(e){}charge.o=null}
const SFX={
  click(){tone(900,600,0.06,'square',0.05)},
  flick(p){ // 「バチィン！」：爪が当たる音＋重低音＋風切り
    noise(0.025,4000,'highpass',0.9);
    noise(0.09,1700,'bandpass',0.7+p*0.5);
    tone(2200,500,0.05,'square',0.12);
    tone(170,38,0.32,'sine',0.5+p*0.5);
    sweep(0.45+p*0.25,500,3500+p*2500,1.2,0.25+p*0.45,0.02);
  },
  max(){tone(1320,1320,0.08,'square',0.07);tone(1760,1760,0.12,'square',0.07,0.07)},
  hit(p){const v=Math.min(1,p/12);noise(0.14,900,'lowpass',0.35+0.6*v);tone(190,45,0.2,'sine',0.25+0.5*v)},
  pencil(p){tone(760,520,0.08,'triangle',0.06+0.15*Math.min(1,p/6));noise(0.04,2500,'bandpass',0.25)},
  ruler(p){tone(340,230,0.13,'triangle',0.1+0.22*Math.min(1,p/8));noise(0.07,1300,'bandpass',0.4)},
  boing(p){const v=Math.min(1,p/10);tone(150,560,0.22,'sine',0.2+0.3*v);tone(560,240,0.25,'sine',0.15+0.2*v,0.16)},
  drop(){tone(900,260,0.55,'sine',0.07)},
  clack(){noise(0.06,2200,'bandpass',0.3);tone(1200,900,0.05,'triangle',0.05)},
  land(p){noise(0.07,600,'lowpass',Math.min(0.45,p/18))},
  jump(){tone(300,950,0.16,'sine',0.15)},
  fall(){tone(1100,140,1.2,'sine',0.22)},
  floor(){noise(0.12,400,'lowpass',0.5);tone(120,55,0.18,'sine',0.35)},
  win(){[60,64,67,72,67,72].forEach((n,i)=>tone(mf(n),mf(n),0.16,'square',0.09,i*0.09));
    [72,76,79,84].forEach(n=>tone(mf(n),mf(n)*1.002,1.1,'sawtooth',0.035,0.55));tone(mf(36),mf(36),1.1,'triangle',0.25,0.55);noise(1.3,4500,'highpass',0.3,0.55)},
  lose(){[392,330,262].forEach((f,i)=>tone(f,f*0.97,0.26,'square',0.08,i*0.2))},
  round(){tone(660,660,0.1,'square',0.06);tone(990,990,0.18,'square',0.06,0.12)},
  tick(){tone(1500,1500,0.05,'square',0.07)},
  creak(){tone(190,140,0.35,'sawtooth',0.05);tone(240,170,0.3,'triangle',0.06,0.14);tone(170,120,0.3,'triangle',0.05,0.3)},
  buzz(){tone(220,110,0.45,'sawtooth',0.12)}
};

// ================= BGM（WebAudioでその場で合成） =================
const mf=n=>440*Math.pow(2,(n-69)/12);
const BGM={on:true,gain:null,bus:null,filt:null,timer:null,cur:null,want:'menu',next:0,step:0,tempo:1,fTarget:20000};

function bgmVol(){if(!BGM.gain)return;BGM.gain.gain.setTargetAtTime(BGM.on?0.36*VOL.bgm:0,AC.currentTime,0.08)}
function bgmEnsure(){
  const a=AC;if(!a||BGM.gain)return;
  BGM.bus=a.createGain();
  BGM.filt=a.createBiquadFilter();BGM.filt.type='lowpass';BGM.filt.frequency.value=20000;BGM.filt.Q.value=5;
  const comp=a.createDynamicsCompressor();comp.threshold.value=-16;comp.ratio.value=4;comp.attack.value=0.004;comp.release.value=0.15;
  BGM.gain=a.createGain();BGM.gain.gain.value=0;
  BGM.bus.connect(BGM.filt).connect(comp).connect(BGM.gain).connect(a.destination);
  BGM.timer=setInterval(bgmTick,25);bgmVol();const w=BGM.want;BGM.want=null;bgmPlay(w);
}
function bgmPlay(name,force){
  if(!force&&BGM.want===name&&BGM.cur===name)return;BGM.want=name;if(!BGM.gain)return;
  BGM.cur=name;BGM.step=0;BGM.next=AC.currentTime+0.06;
}
function bgmTick(){
  const a=AC;if(!a||!BGM.cur||a.state!=='running')return;const T=TRACKS[BGM.cur];
  if(BGM.next<a.currentTime-0.25)BGM.next=a.currentTime+0.02;
  while(BGM.next<a.currentTime+0.12){const sd=60/T.bpm/4*BGM.tempo;try{T.play(BGM.step,BGM.next,sd)}catch(e){}BGM.step++;BGM.next+=sd}
}
// ゲームの展開に合わせて音を動かす（毎フレーム）
let bgmFilt=20000;
function bgmUpdate(){
  if(!BGM.gain)return;
  const ph=game.phase,sub=ph==='wait'?game.remoteSub:ph;let f=20000,tempo=1;
  if(slowT>0){f=900;tempo=2}                                            // 激落スロー：こもって半分の速さ
  else if(sub==='power'&&game.mode)f=700+Math.pow(game.shot.power,2)*15000; // パワーをためるほど開いていく
  BGM.tempo=tempo;
  if(Math.abs(f-bgmFilt)>30){bgmFilt=f;BGM.filt.frequency.setTargetAtTime(f,AC.currentTime,slowT>0?0.05:0.03)}
}
function bgmHit(kind){if(!BGM.gain||!BGM.on||!VOL.bgm)return;const t=AC.currentTime+0.005;
  if(kind==='crash')DR.crash(t,1.1);else if(kind==='boom'){DR.kick(t,1.2);DR.crash(t,0.8)}}
function iOsc(t,type,f,dur,vol,o={}){
  const a=AC,os=a.createOscillator(),g=a.createGain();os.type=type;os.frequency.setValueAtTime(f,t);
  if(o.to)os.frequency.exponentialRampToValueAtTime(o.to,t+(o.toT||dur));if(o.det)os.detune.value=o.det;
  const at=o.att||0.004;g.gain.setValueAtTime(0.0001,t);g.gain.linearRampToValueAtTime(vol,t+at);
  g.gain.setValueAtTime(vol,t+Math.max(at,dur*(o.sus==null?0.3:o.sus)));g.gain.exponentialRampToValueAtTime(0.0001,t+dur);
  let n=os;if(o.lp){const fl=a.createBiquadFilter();fl.type='lowpass';fl.frequency.setValueAtTime(o.lp,t);if(o.lpTo)fl.frequency.exponentialRampToValueAtTime(o.lpTo,t+dur);fl.Q.value=o.q||1;os.connect(fl);n=fl}
  n.connect(g).connect(BGM.bus);os.start(t);os.stop(t+dur+0.03);
}
function iNoise(t,dur,type,freq,vol,q=1){
  const a=AC,sr=a.createBufferSource();sr.buffer=noiseBuf;const f=a.createBiquadFilter();f.type=type;f.frequency.value=freq;f.Q.value=q;
  const g=a.createGain();g.gain.setValueAtTime(vol,t);g.gain.exponentialRampToValueAtTime(0.0001,t+dur);
  sr.connect(f).connect(g).connect(BGM.bus);sr.start(t,Math.random()*0.4);sr.stop(t+dur+0.03);
}
const DR={
  kick(t,v=1){iOsc(t,'sine',165,0.24,0.95*v,{to:42,toT:0.13,sus:0.05});iOsc(t,'triangle',1400,0.02,0.22*v,{to:180})},
  snare(t,v=1){iNoise(t,0.17,'bandpass',1900,0.6*v,0.8);iOsc(t,'triangle',230,0.09,0.32*v,{to:150})},
  clap(t,v=1){iNoise(t,0.13,'bandpass',1300,0.5*v,1.4);iNoise(t+0.012,0.1,'bandpass',1500,0.35*v,1.4)},
  hat(t,v=1,open){iNoise(t,open?0.13:0.03,'highpass',7800,0.2*v)},
  crash(t,v=1){iNoise(t,1.5,'highpass',4200,0.32*v);iNoise(t,0.5,'bandpass',6000,0.18*v)}
};
const bass=(t,n,d,v=1)=>{iOsc(t,'sawtooth',mf(n),d,0.3*v,{lp:1000,lpTo:260,q:5,sus:0.5});iOsc(t,'square',mf(n-12),d,0.13*v,{lp:380,sus:0.5})};
const lead=(t,n,d,v=1)=>{iOsc(t,'square',mf(n),d,0.1*v,{sus:0.75,lp:4600});iOsc(t,'sawtooth',mf(n),d,0.065*v,{det:14,sus:0.75,lp:3200})};
const pluck=(t,n,d,v=1)=>iOsc(t,'square',mf(n),Math.min(d,0.16),0.055*v,{lp:3800,lpTo:900,sus:0.04});
const stab=(t,ns,d,v=1)=>ns.forEach((n,i)=>iOsc(t,'sawtooth',mf(n),d,0.045*v,{lp:2800,lpTo:700,sus:0.1,det:(i-1)*9}));
const bell=(t,n,d,v=1)=>{iOsc(t,'sine',mf(n),d,0.14*v,{sus:0.04});iOsc(t,'triangle',mf(n+12),d*0.5,0.05*v,{sus:0.04})};
// コード（ベースの根音, 上の和音）
const CH={Am:[45,[57,60,64]],F:[41,[53,57,60]],C:[48,[55,60,64]],G:[43,[55,59,62]],E:[40,[56,59,64]],Dm:[38,[57,62,65]]};
// バトル曲のメロディ（小節ごとに [16分の位置, 音, 長さ]）
const BAT_MEL=[
  [[0,76,2],[2,74,2],[4,72,2],[6,74,2],[8,76,4],[12,81,4]],
  [[0,77,3],[3,76,1],[4,74,2],[6,72,2],[8,74,8]],
  [[0,72,2],[2,74,2],[4,76,2],[6,79,2],[8,76,3],[11,74,1],[12,72,4]],
  [[0,74,4],[4,71,2],[6,74,2],[8,79,8]],
  [[0,76,2],[2,74,2],[4,72,2],[6,74,2],[8,76,4],[12,84,4]],
  [[0,81,3],[3,79,1],[4,77,2],[6,76,2],[8,77,4],[12,76,4]],
  [[0,74,2],[2,76,2],[4,79,2],[6,81,2],[8,83,8]],
  [[0,80,6],[6,83,2],[8,88,8]]];
const MENU_MEL=[
  [[0,76,4],[4,79,4],[8,84,6],[14,83,2]],
  [[0,81,4],[4,79,4],[8,74,8]],
  [[0,76,4],[4,72,4],[8,76,4],[12,79,4]],
  [[0,77,6],[6,76,2],[8,74,4],[12,72,4]]];
const TRACKS={
  // 対戦：168BPMで突っ走る
  battle:{bpm:168,play(step,t,sd){
    const bar=(step>>4)%16,s=step&15,B=bar>=8,prog=B?['F','G','Am','Am','F','G','E','E']:['Am','F','C','G','Am','F','G','E'],ch=CH[prog[bar%8]],last=bar%8===7;
    if(step<16){ // 最初の1小節は助走（ハットとスネアのロール）
      DR.hat(t,0.7,s%4===2);if(s>=8)DR.snare(t,0.4+0.07*(s-8));if(s===0)DR.kick(t);return}
    if(s%4===0)DR.kick(t);if(B&&s===14)DR.kick(t,0.7);
    if(s===4||s===12)DR.snare(t);
    if(last&&s>=12)DR.snare(t,0.55+0.12*(s-12));
    DR.hat(t,s%2?0.55:0.9,s%4===2);
    if(s===0&&bar%8===0)DR.crash(t);
    if(s%2===0)bass(t,ch[0]+((s>>1)%2?12:0),sd*1.7);
    if(s%4===2)stab(t,ch[1].map(n=>n+12),sd*1.4,B?1:0.75);
    if(!B){for(const[st,n,l]of BAT_MEL[bar])if(st===s)lead(t,n,sd*l*0.95)}
    else{const tn=ch[1],arp=[tn[0],tn[1],tn[2],tn[0]+12];pluck(t,arp[s%4]+12,sd,s%4===0?1.2:0.9);
      if(s===0)lead(t,tn[2]+12,sd*7.5,0.75);if(s===8)lead(t,tn[1]+12+(bar%2?2:0),sd*7.5,0.75)}
  }},
  // タイトル・メニュー：132BPMの明るいループ
  menu:{bpm:132,play(step,t,sd){
    const bar=(step>>4)%8,s=step&15,ch=CH[['C','G','Am','F'][bar%4]];
    if(s===0||s===8||s===10)DR.kick(t,0.8);
    if(s===4||s===12)DR.clap(t,0.75);
    if(s%2===0)DR.hat(t,0.45,s%4===2);
    if([0,3,6,8,11,14].includes(s))bass(t,ch[0]+12*(s===6||s===14?1:0),sd*1.6,0.85);
    if(s%2===0){const tn=ch[1];pluck(t,[tn[0],tn[1],tn[2],tn[1]][(s>>1)%4]+12,sd*2,0.8)}
    if(bar>=4)for(const[st,n,l]of MENU_MEL[bar-4])if(st===s)bell(t,n,sd*l);
  }}
};
document.addEventListener('visibilitychange',()=>{if(!AC)return;if(document.hidden)AC.suspend();else AC.resume()});

// ================= 3D =================
const cv=$('c');
// preserveDrawingBuffer：PLiCyのサムネイル・スクリーンショットが真っ黒にならないように
const renderer=new THREE.WebGLRenderer({canvas:cv,antialias:true,preserveDrawingBuffer:true});
renderer.setPixelRatio(Math.min(2,window.devicePixelRatio||1));
renderer.shadowMap.enabled=true;renderer.shadowMap.type=THREE.PCFSoftShadowMap;
renderer.outputEncoding=THREE.sRGBEncoding;
const scene=new THREE.Scene();
scene.background=new THREE.Color(0xf2e2c4);
scene.fog=new THREE.Fog(0xf2e2c4,45,120);
const camera=new THREE.PerspectiveCamera(60,1,0.05,300);

scene.add(new THREE.HemisphereLight(0xfff6e5,0x6b5a48,0.8));
const sun=new THREE.DirectionalLight(0xffffff,0.85);
sun.position.set(8,30,10);sun.castShadow=true;sun.shadow.mapSize.set(2048,2048);
Object.assign(sun.shadow.camera,{left:-24,right:24,top:12,bottom:-12,near:1,far:90});
scene.add(sun);scene.add(sun.target);

const redraws=[];
function canvasTex(w,h,draw){const c=document.createElement('canvas');c.width=w;c.height=h;const g=c.getContext('2d');draw(g,w,h);const t=new THREE.CanvasTexture(c);t.encoding=THREE.sRGBEncoding;t.anisotropy=renderer.capabilities.getMaxAnisotropy();t._redraw=()=>{g.setTransform(1,0,0,1,0,0);g.clearRect(0,0,w,h);draw(g,w,h);t.needsUpdate=true};return t}
function makeWood(seed,txt,tx,ty){return canvasTex(1024,666,(g,w,h)=>{
  g.fillStyle='#cf9a5f';g.fillRect(0,0,w,h);const r=mulberry32(seed);
  for(let i=0;i<240;i++){const y=r()*h,amp=3+r()*9,ph=r()*6,f=0.003+r()*0.008;
    g.strokeStyle=`rgba(${110+r()*40|0},${60+r()*25|0},25,${0.12+r()*0.22})`;g.lineWidth=1+r()*3;g.beginPath();
    for(let x=0;x<=w;x+=8){const yy=y+Math.sin(x*f+ph)*amp+Math.sin(x*f*3.1+ph)*amp*0.3;x?g.lineTo(x,yy):g.moveTo(x,yy)}g.stroke()}
  g.fillStyle='rgba(50,50,70,.25)';g.font="bold 40px sans-serif";
  g.save();g.translate(tx,ty);g.rotate(-0.15);g.fillText(txt,0,0);g.restore();
})}
const woodTexes=[makeWood(7,'ここに落書き',120,600),makeWood(19,'ねむい…',760,110)];
const tileTex=canvasTex(256,256,(g,w,h)=>{g.fillStyle='#d9d2c3';g.fillRect(0,0,w,h);g.fillStyle='#c2b8a5';g.fillRect(0,0,w/2,h/2);g.fillRect(w/2,h/2,w/2,h/2);g.strokeStyle='rgba(0,0,0,.08)';g.strokeRect(0,0,w,h)});
tileTex.wrapS=tileTex.wrapT=THREE.RepeatWrapping;tileTex.repeat.set(14,11);
const boardTex=canvasTex(1024,360,(g,w,h)=>{
  g.fillStyle='#2f5d46';g.fillRect(0,0,w,h);const r=mulberry32(3);
  for(let i=0;i<40;i++){g.fillStyle=`rgba(255,255,255,${r()*0.05})`;g.fillRect(r()*w,r()*h,80+r()*200,20+r()*60)}
  g.fillStyle='rgba(255,255,255,.88)';g.font="140px 'Dela Gothic One', sans-serif";g.textAlign='center';g.fillText('激落！！',w/2,170);
  g.font="58px 'Dela Gothic One', sans-serif";g.fillText('消しゴムバトル',w/2,270);
  g.font="34px 'M PLUS Rounded 1c', sans-serif";g.textAlign='left';g.fillText('日直：けしごむ',40,330);
});
const grainTex=canvasTex(256,256,(g,w,h)=>{g.fillStyle='#fff';g.fillRect(0,0,w,h);const r=mulberry32(5);for(let i=0;i<2600;i++){const v=150+r()*90|0;g.fillStyle=`rgb(${v},${v},${v})`;g.fillRect(r()*w,r()*h,1+r()*3,1+r()*3)}});
const sleeveCache={};
function sleeveTex(col,label){const key=col+label;if(sleeveCache[key])return sleeveCache[key];
  const t=canvasTex(512,256,(g,w,h)=>{
    g.fillStyle=col;g.fillRect(0,0,w,h);g.fillStyle='#fff';g.fillRect(0,h*0.1,w,h*0.07);g.fillRect(0,h*0.83,w,h*0.07);
    let fs=118;g.font=`900 ${fs}px 'Dela Gothic One', sans-serif`;const mw=g.measureText(label).width;
    if(mw>430){fs=Math.floor(fs*430/mw);g.font=`900 ${fs}px 'Dela Gothic One', sans-serif`}
    g.textAlign='center';g.textBaseline='middle';
    g.lineWidth=fs*0.12;g.strokeStyle='#1b1430';g.strokeText(label,w/2,h/2+4);g.fillStyle='#fff';g.fillText(label,w/2,h/2+4);
  });redraws.push(t);return sleeveCache[key]=t}
const PLCOL=['#ff4b3e','#2f8cff'];
redraws.push(boardTex);
// 定規の目盛り
const rulerTex=canvasTex(1024,96,(g,w,h)=>{
  g.fillStyle='#c8eefc';g.fillRect(0,0,w,h);g.fillStyle='#1d3b5e';g.font="bold 20px sans-serif";g.textAlign='center';
  for(let i=0;i<=200;i++){const x=24+i*(w-48)/200,l=i%10===0?34:i%5===0?22:12;g.fillRect(x-0.8,0,1.6,l);if(i%10===0&&i<200)g.fillText(String(i/10),x,58)}
  g.font="bold 18px sans-serif";g.textAlign='right';g.fillText('GEKIOCHI 20cm',w-30,86);
});
if(document.fonts&&document.fonts.ready)document.fonts.ready.then(()=>redraws.forEach(t=>t._redraw()));

// ===== ステージ（教室・音楽室・体育館。見た目だけで、ルールは同じ） =====
const STAGE_NAMES=['教室','音楽室','体育館'];
const stageG=[0,1,2].map(()=>{const g=new THREE.Group();scene.add(g);return g});
const roomMat={};
const corkTex=canvasTex(512,256,(g,w,h)=>{g.fillStyle='#b98a55';g.fillRect(0,0,w,h);const r=mulberry32(11);
  for(let i=0;i<900;i++){g.fillStyle=`rgba(${90+r()*60|0},${55+r()*30|0},20,.35)`;g.fillRect(r()*w,r()*h,2,2)}
  const cols=['#fff','#fff7c2','#d8f0ff','#ffe0ec','#e2ffd8'];
  for(let i=0;i<7;i++){const x=20+i*70+r()*10,y=20+r()*60,pw=56,ph=70+r()*40;g.fillStyle=cols[i%5];g.fillRect(x,y,pw,ph);
    g.fillStyle='rgba(60,60,80,.45)';for(let l=0;l<5;l++)g.fillRect(x+6,y+12+l*12,pw-12-r()*16,3);g.fillStyle='#e23b3b';g.beginPath();g.arc(x+pw/2,y+4,4,0,7);g.fill()}
  g.fillStyle='#fff';g.fillRect(200,180,120,50);g.fillStyle='#1b1430';g.font="bold 26px sans-serif";g.textAlign='center';g.fillText('今月の目標',260,205);g.font="18px sans-serif";g.fillText('机から落ちない',260,226)});
const clockTex=canvasTex(256,256,(g,w,h)=>{g.fillStyle='#fff';g.beginPath();g.arc(128,128,124,0,7);g.fill();g.lineWidth=12;g.strokeStyle='#333';g.stroke();
  g.fillStyle='#333';for(let i=0;i<12;i++){const a=i*Math.PI/6;g.fillRect(128+Math.cos(a)*100-4,128+Math.sin(a)*100-4,8,8)}
  g.lineCap='round';g.lineWidth=10;g.beginPath();g.moveTo(128,128);g.lineTo(128,62);g.stroke();g.lineWidth=7;g.beginPath();g.moveTo(128,128);g.lineTo(188,140);g.stroke()});
// 音楽室
const holeTex=canvasTex(256,256,(g,w,h)=>{g.fillStyle='#f4f1ea';g.fillRect(0,0,w,h);g.fillStyle='#c9c2b4';for(let y=8;y<h;y+=16)for(let x=8;x<w;x+=16){g.beginPath();g.arc(x,y,2.4,0,7);g.fill()}});
holeTex.wrapS=holeTex.wrapT=THREE.RepeatWrapping;holeTex.repeat.set(10,6);
const carpetTex=canvasTex(256,256,(g,w,h)=>{g.fillStyle='#7a2433';g.fillRect(0,0,w,h);const r=mulberry32(9);for(let i=0;i<5000;i++){g.fillStyle=`rgba(${r()<.5?0:255},0,${r()*60|0},${r()*0.08})`;g.fillRect(r()*w,r()*h,2,2)}});
carpetTex.wrapS=carpetTex.wrapT=THREE.RepeatWrapping;carpetTex.repeat.set(10,8);
const staffTex=canvasTex(1024,360,(g,w,h)=>{g.fillStyle='#2f5d46';g.fillRect(0,0,w,h);g.strokeStyle='rgba(255,255,255,.75)';g.lineWidth=3;
  for(const y0 of[60,210])for(let l=0;l<5;l++){g.beginPath();g.moveTo(30,y0+l*18);g.lineTo(w-30,y0+l*18);g.stroke()}
  const r=mulberry32(4);g.fillStyle='rgba(255,255,255,.88)';
  for(const y0 of[60,210])for(let i=0;i<14;i++){const x=110+i*62,y=y0+((r()*9)|0)*9;g.beginPath();g.ellipse(x,y,10,7,-0.4,0,7);g.fill();g.fillRect(x+8,y-46,3,46)}
  g.font="bold 64px serif";g.fillText('♪',40,140);g.font="34px 'M PLUS Rounded 1c', sans-serif";g.fillText('きょうの歌：けしごむのうた',40,345)});
const portraitTex=canvasTex(256,320,(g,w,h)=>{g.fillStyle='#5a3a1e';g.fillRect(0,0,w,h);g.fillStyle='#2a2430';g.fillRect(16,16,w-32,h-80);
  g.fillStyle='#d9c7a8';g.beginPath();g.arc(w/2,110,46,0,7);g.fill();g.beginPath();g.ellipse(w/2,232,82,52,0,Math.PI,0);g.fill();
  g.fillStyle='#f1ead8';g.beginPath();for(let i=0;i<9;i++)g.arc(w/2-48+i*12,72+Math.sin(i)*6,14,0,7);g.fill();
  g.fillStyle='#e8dcc0';g.fillRect(40,h-54,w-80,34);g.fillStyle='#3a2a18';g.font="bold 22px sans-serif";g.textAlign='center';g.fillText('なぞの作曲家',w/2,h-30)});
const curtainTex=canvasTex(256,64,(g,w,h)=>{for(let x=0;x<w;x++){const v=Math.sin(x/w*Math.PI*8);g.fillStyle=`rgb(${150+v*40|0},${22+v*10|0},${34+v*10|0})`;g.fillRect(x,0,1,h)}});
// 体育館
const gymFloorTex=canvasTex(1024,1024,(g,w,h)=>{g.fillStyle='#e0b67c';g.fillRect(0,0,w,h);const r=mulberry32(21);
  for(let y=0;y<h;y+=24){for(let x=-(r()*200|0);x<w;x+=180+r()*120){g.fillStyle=`rgba(${120+r()*40|0},${70+r()*30|0},30,${0.08+r()*0.12})`;g.fillRect(x,y,180,23);g.fillStyle='rgba(90,50,20,.25)';g.fillRect(x,y,2,23)}g.fillStyle='rgba(90,50,20,.18)';g.fillRect(0,y+23,w,1)}
  g.strokeStyle='#fff';g.lineWidth=7;g.strokeRect(150,180,724,664);g.beginPath();g.moveTo(512,180);g.lineTo(512,844);g.stroke();g.beginPath();g.arc(512,512,80,0,7);g.stroke();
  g.strokeStyle='#e23b3b';for(const x of[150,874]){g.beginPath();g.arc(x,512,190,x<512?-Math.PI/2:Math.PI/2,x<512?Math.PI/2:Math.PI*1.5);g.stroke()}
  g.strokeStyle='#2f8cff';g.strokeRect(60,90,904,844)});
const gymWallTex=canvasTex(256,512,(g,w,h)=>{g.fillStyle='#ecebe6';g.fillRect(0,0,w,h);g.fillStyle='#dcdad3';g.fillRect(0,0,w,40);
  g.fillStyle='#b98c5a';g.fillRect(0,h*0.72,w,h*0.28);g.fillStyle='rgba(80,50,20,.3)';for(let x=0;x<w;x+=32)g.fillRect(x,h*0.72,2,h*0.28);g.fillRect(0,h*0.72,w,4)});
gymWallTex.wrapS=THREE.RepeatWrapping;gymWallTex.repeat.set(6,1);
const ballTex=canvasTex(256,128,(g,w,h)=>{g.fillStyle='#e8742a';g.fillRect(0,0,w,h);g.strokeStyle='#2a1a10';g.lineWidth=4;g.beginPath();g.moveTo(0,h/2);g.lineTo(w,h/2);g.stroke();
  for(const x of[w/4,w*3/4]){g.beginPath();g.moveTo(x,0);g.lineTo(x,h);g.stroke()}g.beginPath();g.ellipse(w/2,h/2,40,h/2,0,0,7);g.stroke()});
redraws.push(staffTex,corkTex,portraitTex);
const STAGE_LOOK=[
  {bg:0xf2e2c4,wall:{color:0xf3e6cc,map:null},floor:tileTex},
  {bg:0xefe6dc,wall:{color:0xffffff,map:holeTex},floor:carpetTex},
  {bg:0xe9e7e0,wall:{color:0xffffff,map:gymWallTex},floor:gymFloorTex}];
function setStage(i){i=clamp(i|0,0,2);game.stage=i;stageG.forEach((g,k)=>g.visible=k===i);const L=STAGE_LOOK[i];
  roomMat.wall.color.setHex(L.wall.color);roomMat.wall.map=L.wall.map;roomMat.wall.needsUpdate=true;roomMat.floor.map=L.floor;roomMat.floor.needsUpdate=true;
  scene.background.setHex(L.bg);scene.fog.color.setHex(L.bg)}
function buildStages(){
  const lam=(o)=>new THREE.MeshLambertMaterial(o),std=(o)=>new THREE.MeshStandardMaterial(o);
  const add=(G,geo,mat,x,y,z,ry=0,cast=false)=>{const m=new THREE.Mesh(geo,mat);m.position.set(x,y,z);m.rotation.y=ry;if(cast)m.castShadow=true;G.add(m);return m};
  // ---- 音楽室 ----
  {const G=stageG[1];
    add(G,new THREE.PlaneGeometry(42,14.8),lam({map:staffTex}),0,6,-44.5);
    add(G,new THREE.BoxGeometry(43.5,16,0.4),lam({color:0x8a6a45}),0,6,-44.95);
    for(let k=0;k<5;k++)add(G,new THREE.PlaneGeometry(7,8.75),lam({map:portraitTex}),-54.8,17,-28+k*14,Math.PI/2);
    const win=new THREE.MeshBasicMaterial({color:0xdff3ff}),cur=lam({map:curtainTex});
    for(let k=-1;k<=1;k++){add(G,new THREE.PlaneGeometry(20,20),win,54.8,8,k*26,-Math.PI/2);
      for(const sd of[-1,1])add(G,new THREE.PlaneGeometry(5,24),cur,54.6,7,k*26+sd*11,-Math.PI/2)}
    // グランドピアノ（かんたんな形）
    const blk=std({color:0x111116,roughness:0.25,metalness:0.1}),wht=lam({color:0xfafafa});
    const pg=new THREE.Group();pg.position.set(-34,FLOOR,-30);pg.rotation.y=0.5;G.add(pg);
    const body=new THREE.Mesh(new THREE.CylinderGeometry(11,11,6,28,1,false,0,Math.PI),blk);body.rotation.y=Math.PI/2;body.position.set(0,24,0);body.scale.set(1,1,1.6);pg.add(body);
    const bx=new THREE.Mesh(new THREE.BoxGeometry(22,6,6),blk);bx.position.set(0,24,-3);pg.add(bx);
    const keys=new THREE.Mesh(new THREE.BoxGeometry(22,1,4),wht);keys.position.set(0,22.5,-8);pg.add(keys);
    const lid=new THREE.Mesh(new THREE.BoxGeometry(22,0.4,18),blk);lid.position.set(0,32,5);lid.rotation.x=-0.6;pg.add(lid);
    for(const[x,z]of[[-9,-3],[9,-3],[0,14]]){const l=new THREE.Mesh(new THREE.CylinderGeometry(1,0.8,21,10),blk);l.position.set(x,10.5,z);pg.add(l)}
    // 譜面台
    const st=std({color:0x333338,metalness:0.6,roughness:0.4});const ms=new THREE.Group();ms.position.set(36,FLOOR,30);G.add(ms);
    const pole=new THREE.Mesh(new THREE.CylinderGeometry(0.4,0.4,30,8),st);pole.position.y=15;ms.add(pole);
    const desk=new THREE.Mesh(new THREE.BoxGeometry(10,7,0.4),st);desk.position.set(0,31,0);desk.rotation.x=-0.4;ms.add(desk);
  }
  // ---- 体育館 ----
  {const G=stageG[2];
    // バスケットゴール（机の先の壁）
    const bb=lam({color:0xffffff}),red=lam({color:0xe23b3b});
    add(G,new THREE.BoxGeometry(0.6,12,18),bb,54.5,20,0);add(G,new THREE.BoxGeometry(0.4,5,7),red,54.1,17.5,0);add(G,new THREE.BoxGeometry(0.5,4,6),bb,53.9,17.5,0);
    const rim=new THREE.Mesh(new THREE.TorusGeometry(3.4,0.25,8,28),std({color:0xff6a1a,metalness:0.4,roughness:0.5}));rim.rotation.x=Math.PI/2;rim.position.set(50,15,0);G.add(rim);
    const net=new THREE.Mesh(new THREE.CylinderGeometry(3.3,2.2,4.5,14,1,true),new THREE.MeshBasicMaterial({color:0xffffff,wireframe:true}));net.position.set(50,12.6,0);G.add(net);
    add(G,new THREE.BoxGeometry(4,0.4,0.4),std({color:0xff6a1a}),52.2,15,0);
    // 高い窓
    const win=new THREE.MeshBasicMaterial({color:0xdff3ff});
    for(let k=-3;k<=3;k++){add(G,new THREE.PlaneGeometry(9,7),win,k*14,36,-44.8);add(G,new THREE.PlaneGeometry(9,7),win,k*14,36,44.8,Math.PI)}
    // ステージ（うしろの壁）
    add(G,new THREE.BoxGeometry(12,10,70),lam({color:0x8a5a33}),-49,FLOOR+5,0);
    const cur=lam({map:curtainTex});cur.map=curtainTex;
    for(const sd of[-1,1])add(G,new THREE.PlaneGeometry(14,36),cur,-54.7,FLOOR+28,sd*26,Math.PI/2);
    add(G,new THREE.PlaneGeometry(70,6),cur,-54.6,FLOOR+44,0,Math.PI/2);
    add(G,new THREE.PlaneGeometry(36,30),lam({color:0x3a2a3a}),-54.8,FLOOR+25,0,Math.PI/2);
    // ボールと跳び箱
    const ballM=std({map:ballTex,roughness:0.7});
    for(const[x,z]of[[30,32],[36,26],[-30,-34],[22,-36]]){const b=add(G,new THREE.SphereGeometry(4.3,24,16),ballM,x,FLOOR+4.3,z,Math.random()*6,true)}
    const tb=new THREE.Group();tb.position.set(-30,FLOOR,30);tb.rotation.y=0.3;G.add(tb);
    for(let i=0;i<5;i++){const m=new THREE.Mesh(new THREE.BoxGeometry(16-i*0.6,3.6,9-i*0.3),lam({color:i===4?0xffffff:0xc89a63}));m.position.y=1.8+i*3.6;m.castShadow=true;tb.add(m)}
  }
}
// 部屋
{
  const wall=new THREE.MeshLambertMaterial({color:0xf3e6cc,side:THREE.BackSide});
  const ceil=new THREE.MeshLambertMaterial({color:0xffffff,side:THREE.BackSide});
  const floor=new THREE.MeshLambertMaterial({map:tileTex,side:THREE.BackSide});
  const room=new THREE.Mesh(new THREE.BoxGeometry(110,70,90),[wall,wall,ceil,floor,wall,wall]);
  room.position.y=FLOOR+35;scene.add(room);
  const fl=new THREE.Mesh(new THREE.PlaneGeometry(110,90),new THREE.ShadowMaterial({opacity:0.25}));fl.rotation.x=-Math.PI/2;fl.position.y=FLOOR+0.02;fl.receiveShadow=true;scene.add(fl);
  roomMat.wall=wall;roomMat.floor=floor;
  const G=stageG[0];
  const board=new THREE.Mesh(new THREE.PlaneGeometry(42,14.8),new THREE.MeshLambertMaterial({map:boardTex}));board.position.set(0,6,-44.5);G.add(board);
  const frame=new THREE.Mesh(new THREE.BoxGeometry(43.5,16,0.4),new THREE.MeshLambertMaterial({color:0x8a6a45}));frame.position.set(0,6,-44.95);G.add(frame);
  const win=new THREE.MeshBasicMaterial({color:0xcfefff});
  for(let k=-1;k<=1;k++){const m=new THREE.Mesh(new THREE.PlaneGeometry(22,20),win);m.position.set(54.8,8,k*26);m.rotation.y=-Math.PI/2;G.add(m)}
  // 教室：うしろの掲示板と時計
  const cork=new THREE.Mesh(new THREE.PlaneGeometry(40,16),new THREE.MeshLambertMaterial({map:corkTex}));cork.position.set(-54.8,6,0);cork.rotation.y=Math.PI/2;G.add(cork);
  const clock=new THREE.Mesh(new THREE.CircleGeometry(3.2,32),new THREE.MeshLambertMaterial({map:clockTex}));clock.position.set(0,19,-44.5);G.add(clock);
}
buildStages();
// 机（2台）
{
  const side=new THREE.MeshStandardMaterial({color:0x8d5a2f,roughness:0.8});
  const metal=new THREE.MeshStandardMaterial({color:0x8f9aa6,metalness:0.6,roughness:0.4});
  DESKS.forEach((d,i)=>{
    const w=d.x1-d.x0,dp=d.z1-d.z0,cx=(d.x0+d.x1)/2,cz=(d.z0+d.z1)/2;
    const top=new THREE.MeshStandardMaterial({map:woodTexes[i],roughness:0.75});
    const desk=new THREE.Mesh(new THREE.BoxGeometry(w-0.04,1,dp),[side,side,top,side,side,side]);
    desk.position.set(cx,-0.5,cz);desk.receiveShadow=true;desk.castShadow=true;scene.add(desk);
    const frame=new THREE.Mesh(new THREE.BoxGeometry(w-1,1.2,dp-1),metal);frame.position.set(cx,-1.6,cz);scene.add(frame);
    // 引き出しスペース
    const box=new THREE.Mesh(new THREE.BoxGeometry(w-1.6,1.6,dp-2.2),new THREE.MeshStandardMaterial({color:0x6f7882,metalness:0.4,roughness:0.6}));box.position.set(cx,-2.8,cz);scene.add(box);
    for(const sx of[-1,1])for(const sz of[-1,1]){const l=new THREE.Mesh(new THREE.CylinderGeometry(0.35,0.35,24,12),metal);l.position.set(cx+sx*(w/2-1.1),-13,cz+sz*(dp/2-1.1));l.castShadow=true;scene.add(l)}
  });
}
// 消しゴムの形：角の丸い箱（noiseで使い古しのいびつさ）
function roundBox(w,h,d,r,noise=0,seed=1){
  const seg=r>0.15?18:8,g=new THREE.BoxGeometry(w,h,d,seg,seg,seg),p=g.attributes.position,v=new THREE.Vector3(),c=new THREE.Vector3(),rnd=mulberry32(seed);
  const hx=w/2-r,hy=h/2-r,hz=d/2-r;
  for(let i=0;i<p.count;i++){v.fromBufferAttribute(p,i);c.set(clamp(v.x,-hx,hx),clamp(v.y,-hy,hy),clamp(v.z,-hz,hz));
    const o=v.clone().sub(c);if(o.lengthSq()>0)v.copy(c).add(o.normalize().multiplyScalar(r));
    if(noise){const n=(Math.sin(v.x*7.1+seed)+Math.sin(v.z*9.3+seed*2)+Math.sin(v.y*11.7))*noise;v.multiplyScalar(1+n)}
    p.setXYZ(i,v.x,v.y,v.z)}
  g.computeVertexNormals();return g}
const BODY_GEO={};
const bodyGeo=k=>BODY_GEO[k]||(BODY_GEO[k]=roundBox(EL,EH,EW,ETYPES[k].rr||0.05,ETYPES[k].worn?0.007:0,k+3));
// 使い古しの黒ずみ・ブッとびのしま模様
const grimeTex=canvasTex(256,128,(g,w,h)=>{g.fillStyle='#fff';g.fillRect(0,0,w,h);const r=mulberry32(17);
  for(let i=0;i<120;i++){const x=r()*w,y=r()*h,rad=3+r()*16;const gr=g.createRadialGradient(x,y,0,x,y,rad);gr.addColorStop(0,`rgba(80,80,90,${0.04+r()*0.12})`);gr.addColorStop(1,'rgba(70,70,80,0)');g.fillStyle=gr;g.fillRect(x-rad,y-rad,rad*2,rad*2)}
  g.strokeStyle='rgba(60,60,70,.35)';g.lineWidth=1.5;for(let i=0;i<14;i++){g.beginPath();const x=r()*w,y=r()*h;g.moveTo(x,y);g.lineTo(x+(r()-.5)*60,y+(r()-.5)*20);g.stroke()}});
const stripeTex=canvasTex(128,128,(g,w,h)=>{g.fillStyle='#fff';g.fillRect(0,0,w,h);g.fillStyle='rgba(255,90,20,.85)';for(let y=-h;y<h*2;y+=32){g.beginPath();g.moveTo(0,y);g.lineTo(w,y+40);g.lineTo(w,y+54);g.lineTo(0,y+14);g.fill()}});
stripeTex.wrapS=stripeTex.wrapT=THREE.RepeatWrapping;stripeTex.repeat.set(2,1);
// 消しゴム
function makeEraser(i){
  const g=new THREE.Group();g.rotation.order='YXZ';
  const body=new THREE.Mesh(new THREE.BoxGeometry(EL,EH,EW),new THREE.MeshStandardMaterial({color:0xf7f6f0,roughness:0.95}));
  body.castShadow=body.receiveShadow=true;g.add(body);
  const sl=new THREE.Mesh(new THREE.BoxGeometry(EL*0.62,EH+0.04,EW+0.04),new THREE.MeshStandardMaterial({map:sleeveTex(PLCOL[i],'激落'),roughness:0.65}));
  sl.castShadow=true;g.add(sl);
  const smudge=new THREE.Mesh(new THREE.BoxGeometry(0.02,EH*0.7,EW*0.7),new THREE.MeshStandardMaterial({color:0x9b9ba8,roughness:1}));
  smudge.position.x=EL/2;g.add(smudge);g.userData.smudge=smudge;
  scene.add(g);
  const ring=new THREE.Mesh(new THREE.RingGeometry(0.95,1.15,40),new THREE.MeshBasicMaterial({color:i?0x2f8cff:0xff4b3e,transparent:true,opacity:0.6,depthWrite:false}));
  ring.rotation.x=-Math.PI/2;scene.add(ring);
  return{g,ring,body,sl,smudge,vib:0,jelly:false};
}
const eMesh=[makeEraser(0),makeEraser(1)];
// ===== ガチャ景品（見た目と称号だけ。性能は変わらない） =====
const RAR=['ノーマル','レア','激レア','伝説','勝ち抜き','特殊'];
const SKINS={
  s1:{name:'すいか',rar:0,body:0x57c26a,sleeve:'#e23b3b',tex:'melon',rough:0.5},s2:{name:'チョコ',rar:0,body:0x7a4a2b,sleeve:'#c79a5b',tex:'choco',rough:0.35},
  s3:{name:'ソーダ',rar:0,body:0x9be8ff,sleeve:'#1c7ed6',tex:'soda',rough:0.15,clear:0.85},s4:{name:'さくら',rar:0,body:0xffd6e6,sleeve:'#ff6fa5',tex:'sakura',rough:0.6},
  s5:{name:'まっくろ',rar:1,body:0x2a2a33,sleeve:'#55556a',tex:'night',rough:0.45},s6:{name:'ほのお',rar:1,body:0xff7a1a,sleeve:'#b01212',emis:0x7a2000,tex:'fire',rough:0.5,emisTex:1},
  s7:{name:'ぎんいろ',rar:2,body:0xc9d1da,sleeve:'#2c333d',tex:'silver',rough:0.25,metal:0.3,emis:0x30343a},s8:{name:'にじいろ',rar:2,body:0xff6ad5,sleeve:'#7b2ff7',tex:'rainbow',rough:0.3,anim:3},
  s9:{name:'まぼろし',rar:3,body:0xbfe6ff,sleeve:'#2a1d6e',emis:0x2a4fb0,anim:2,tex:'ghost'},
  // 特殊スキン（おもちゃっぽい形。見た目だけで性能は元の消しゴムのまま）
  x1:{name:'カブトムシ',rar:5,body:0x5a2e12,sleeve:'#3a1d0a',model:'beetle'},x7:{name:'王冠',rar:4,body:0xffc928,sleeve:'#c21f3a',model:'crown'},
  x3:{name:'レンガ',rar:5,body:0xc0532f,sleeve:'#7a2f18',model:'brick'},x4:{name:'たまご寿司',rar:5,body:0xffd23f,sleeve:'#1b1430',model:'sushi'},
  x5:{name:'将棋の駒',rar:5,body:0xe8c27a,sleeve:'#3a2410',model:'shogi'},x6:{name:'牛乳パック',rar:5,body:0xffffff,sleeve:'#2f8cff',model:'milk'},
  x8:{name:'ハンバーガー',rar:5,body:0xd99a4e,sleeve:'#7a3d12',model:'burger'},x9:{name:'招き猫',rar:5,body:0xffffff,sleeve:'#e23b3b',model:'maneki'},
  x10:{name:'こんにゃく',rar:5,body:0x8d8a86,sleeve:'#4a4744',model:'konnyaku',jelly:1},x11:{name:'土下座サラリーマン',rar:5,body:0x26324f,sleeve:'#26324f',model:'dogeza'},
  x12:{name:'プリン',rar:5,body:0xffd977,sleeve:'#7a3d12',model:'pudding',jelly:1}};
const TITLES={
  t1:{name:'かけだし',rar:0},t2:{name:'文房具マニア',rar:0},t3:{name:'えんぴつ派',rar:0},t4:{name:'定規使い',rar:0},
  t5:{name:'ギリギリ職人',rar:1},t6:{name:'机の端の住人',rar:1},t7:{name:'消しカス長者',rar:2},t8:{name:'休み時間の覇者',rar:2},
  t9:{name:'伝説の消しゴム',rar:3},
  t10:{name:'激落王を倒した者',rar:4},t11:{name:'勝ち抜きの鬼',rar:4}};
const PRIZES=Object.assign({},SKINS,TITLES),safeSkin=v=>SKINS[v]?v:'',safeTitle=v=>TITLES[v]?v:'';
const MY={skin:'',title:''};try{MY.skin=safeSkin(SAVE.getItem('gekiochiSkin'));MY.title=safeTitle(SAVE.getItem('gekiochiTitle'))}catch(e){}
const skinOf=i=>i===(game.mode==='cpu'?0:game.me)?MY.skin:safeSkin(game.oppSkin),titleOf=i=>i===(game.mode==='cpu'?0:game.me)?MY.title:safeTitle(game.oppTitle);
function applyLooks(types){
  types.forEach((k,i)=>{const T=Object.assign({},ETYPES[k],k!==3?SKINS[skinOf(i)]:null),m=eMesh[i],E=ETYPES[k];m.anim=T.anim|0;T.label=E.label;
    const sid=k!==3?skinOf(i):'',SK=SKINS[sid]||null,mdl=SK&&SK.model?skinModel(m,sid):null;
    if(m.models)for(const id in m.models)m.models[id].visible=m.models[id]===mdl;
    m.body.visible=m.sl.visible=!mdl;
    m.body.geometry=bodyGeo(k);m.smudge.visible=!mdl&&(E.rr||0)<0.12;m.jelly=!!E.jelly||!!(SK&&SK.jelly);m.skinTex=SK&&SK.tex?skinTex(SK.tex):null;
    const clear=SK&&SK.clear?SK.clear:(!!E.clear&&!SK)?0.82:0;m.body.material.transparent=m.anim===2||!!clear;m.body.material.opacity=clear||1;m.body.material.depthWrite=m.anim!==2;
    m.body.material.color.setHex(m.skinTex?0xffffff:T.body);m.body.material.map=m.skinTex||(E.worn?grimeTex:E.stripe?stripeTex:T.grain?grainTex:null);m.body.material.needsUpdate=true;
    m.body.material.roughness=SK&&SK.rough!=null?SK.rough:E.clear?0.06:T.rough;m.body.material.metalness=SK&&SK.metal!=null?SK.metal:E.clear?0.15:(T.metal||0);m.body.material.emissive.setHex(T.emis||0);
    m.body.material.emissiveMap=SK&&SK.emisTex?m.skinTex:null;
    m.sl.material.map=sleeveTex(T.sleeve||PLCOL[i],T.label);m.sl.material.needsUpdate=true;});
}
// ===== スキンの模様 =====
const SKIN_TEX={};
const skinTex=n=>SKIN_TEX[n]||(SKIN_TEX[n]=({
  melon:()=>canvasTex(256,128,(g,w,h)=>{g.fillStyle='#4fb860';g.fillRect(0,0,w,h);g.fillStyle='#1f6e33';
    for(let x=-20;x<w+20;x+=36){g.beginPath();for(let y=0;y<=h;y+=8)g.lineTo(x+Math.sin(y*0.18+x)*7,y);for(let y=h;y>=0;y-=8)g.lineTo(x+14+Math.sin(y*0.18+x+1)*7,y);g.fill()}}),
  choco:()=>canvasTex(256,128,(g,w,h)=>{g.fillStyle='#6b3d22';g.fillRect(0,0,w,h);for(let x=0;x<w;x+=64)for(let y=0;y<h;y+=64){
    g.fillStyle='#7d4a2b';g.fillRect(x+6,y+6,52,52);g.fillStyle='rgba(255,255,255,.12)';g.fillRect(x+6,y+6,52,6);g.fillStyle='rgba(0,0,0,.25)';g.fillRect(x+6,y+52,52,6)}}),
  soda:()=>canvasTex(256,128,(g,w,h)=>{const gr=g.createLinearGradient(0,0,0,h);gr.addColorStop(0,'#c9f3ff');gr.addColorStop(1,'#7fd6f5');g.fillStyle=gr;g.fillRect(0,0,w,h);
    const r=mulberry32(3);g.strokeStyle='rgba(255,255,255,.9)';g.lineWidth=2.5;for(let i=0;i<40;i++){g.beginPath();g.arc(r()*w,r()*h,2+r()*7,0,7);g.stroke()}}),
  sakura:()=>canvasTex(256,128,(g,w,h)=>{g.fillStyle='#ffe3ee';g.fillRect(0,0,w,h);const r=mulberry32(8);
    for(let i=0;i<14;i++){const x=r()*w,y=r()*h,s=6+r()*6;g.fillStyle=r()<.5?'#ff9ec4':'#ffbcd6';for(let k=0;k<5;k++){const a=k*Math.PI*2/5+r();g.beginPath();g.ellipse(x+Math.cos(a)*s,y+Math.sin(a)*s,s*0.7,s*0.45,a,0,7);g.fill()}
      g.fillStyle='#fff3a0';g.beginPath();g.arc(x,y,s*0.35,0,7);g.fill()}}),
  night:()=>canvasTex(256,128,(g,w,h)=>{g.fillStyle='#22222c';g.fillRect(0,0,w,h);const r=mulberry32(12);for(let i=0;i<70;i++){g.fillStyle=`rgba(255,255,255,${0.3+r()*0.6})`;const x=r()*w,y=r()*h,s=r()<.12?2.4:1;g.fillRect(x,y,s,s)}}),
  fire:()=>canvasTex(256,128,(g,w,h)=>{const gr=g.createLinearGradient(0,h,0,0);gr.addColorStop(0,'#ffe066');gr.addColorStop(0.45,'#ff8a1a');gr.addColorStop(1,'#c4160e');g.fillStyle=gr;g.fillRect(0,0,w,h);
    g.fillStyle='rgba(255,240,150,.85)';for(let x=0;x<w;x+=40){g.beginPath();g.moveTo(x,h);g.quadraticCurveTo(x+6,h*0.45,x+20,h*0.25);g.quadraticCurveTo(x+18,h*0.6,x+40,h);g.fill()}}),
  silver:()=>canvasTex(256,128,(g,w,h)=>{const gr=g.createLinearGradient(0,0,0,h);gr.addColorStop(0,'#f4f7fa');gr.addColorStop(0.5,'#c3ccd6');gr.addColorStop(1,'#e8edf2');g.fillStyle=gr;g.fillRect(0,0,w,h);const r=mulberry32(6);for(let i=0;i<120;i++){g.fillStyle=`rgba(255,255,255,${0.15+r()*0.25})`;g.fillRect(0,r()*h,w,1)}}),
  rainbow:()=>{const t=canvasTex(256,64,(g,w,h)=>{const c=['#ff4b3e','#ff9f1a','#ffd23f','#3ccf6b','#2f8cff','#8a4bff','#ff4b3e'];const gr=g.createLinearGradient(0,0,w,0);c.forEach((x,i)=>gr.addColorStop(i/6,x));g.fillStyle=gr;g.fillRect(0,0,w,h);
    g.fillStyle='rgba(255,255,255,.35)';g.fillRect(0,0,w,h*0.3)});t.wrapS=THREE.RepeatWrapping;return t},
  ghost:()=>canvasTex(128,128,(g,w,h)=>{const gr=g.createRadialGradient(w/2,h/2,4,w/2,h/2,w*0.7);gr.addColorStop(0,'#ffffff');gr.addColorStop(1,'#9fd2ff');g.fillStyle=gr;g.fillRect(0,0,w,h)}),
})[n]());
// ===== 特殊スキン：おもちゃっぽい形（大きさは消しゴムと同じ箱 1.8×0.7×1.0 の中） =====
const SKIN_MODEL={};
function toyMat(c,o={}){return new THREE.MeshStandardMaterial(Object.assign({color:c,roughness:0.38,metalness:0},o))}
function faceTex(bg){return canvasTex(128,128,(g,w,h)=>{g.fillStyle=bg;g.fillRect(0,0,w,h);g.fillStyle='#1b1430';
  g.beginPath();g.arc(42,56,9,0,7);g.arc(86,56,9,0,7);g.fill();g.fillStyle='#fff';g.beginPath();g.arc(45,53,3,0,7);g.arc(89,53,3,0,7);g.fill();
  g.strokeStyle='#1b1430';g.lineWidth=5;g.lineCap='round';g.beginPath();g.arc(64,70,12,0.2,Math.PI-0.2);g.stroke();
  g.fillStyle='rgba(255,120,140,.55)';g.beginPath();g.ellipse(28,76,9,5,0,0,7);g.ellipse(100,76,9,5,0,0,7);g.fill()})}
function textTex(txt,bg,fg,font){return canvasTex(256,128,(g,w,h)=>{g.fillStyle=bg;g.fillRect(0,0,w,h);g.fillStyle=fg;g.font=font;g.textAlign='center';g.textBaseline='middle';g.fillText(txt,w/2,h/2+4)})}
const MODELS={
  beetle(){const G=new THREE.Group(),sh=toyMat(0x6b3414,{roughness:0.15}),dk=toyMat(0x2b170b,{roughness:0.22});
    const limb=(a,b,r)=>{const A=new THREE.Vector3(...a),B=new THREE.Vector3(...b),L=A.distanceTo(B),m=new THREE.Mesh(new THREE.CylinderGeometry(r,r*0.8,L,8),dk);
      m.position.copy(A).add(B).multiplyScalar(0.5);m.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0),B.clone().sub(A).normalize());G.add(m)};
    const shell=new THREE.Mesh(new THREE.SphereGeometry(0.5,36,24),sh);shell.scale.set(1.2,0.62,0.92);shell.position.set(-0.28,0.0,0);G.add(shell);
    const seam=new THREE.Mesh(new THREE.TorusGeometry(0.5,0.012,6,48,Math.PI),dk);seam.scale.set(1.2,0.62,1);seam.position.set(-0.28,0.0,0);G.add(seam);
    const thorax=new THREE.Mesh(new THREE.SphereGeometry(0.34,28,18),dk);thorax.scale.set(0.85,0.72,1.05);thorax.position.set(0.36,0.0,0);G.add(thorax);
    const head=new THREE.Mesh(new THREE.SphereGeometry(0.2,20,14),dk);head.position.set(0.66,-0.07,0);G.add(head);
    const horn=new THREE.Mesh(new THREE.TubeGeometry(new THREE.QuadraticBezierCurve3(new THREE.Vector3(0.68,-0.02,0),new THREE.Vector3(0.98,0.0,0),new THREE.Vector3(1.0,0.36,0)),16,0.055,8),dk);G.add(horn);
    for(const sz of[-1,1]){const t=new THREE.Mesh(new THREE.ConeGeometry(0.045,0.16,8),dk);t.position.set(1.0,0.4,sz*0.05);t.rotation.x=sz*0.5;G.add(t)}
    const horn2=new THREE.Mesh(new THREE.ConeGeometry(0.06,0.3,10),dk);horn2.position.set(0.5,0.25,0);horn2.rotation.z=-0.9;G.add(horn2);
    for(const sz of[-1,1]){for(const[x,dx]of[[-0.45,-0.25],[-0.1,0.0],[0.3,0.25]]){limb([x,-0.08,sz*0.36],[x+dx,-0.16,sz*0.62],0.035);limb([x+dx,-0.16,sz*0.62],[x+dx*1.4,-0.34,sz*0.7],0.03)}
      const e=new THREE.Mesh(new THREE.SphereGeometry(0.05,12,8),toyMat(0xffffff));e.position.set(0.76,-0.03,sz*0.13);G.add(e)}
    const hi=new THREE.Mesh(new THREE.SphereGeometry(0.14,16,10),toyMat(0xffffff,{transparent:true,opacity:0.45}));hi.scale.set(2,0.25,0.6);hi.position.set(-0.38,0.29,0.18);G.add(hi);
    return G},
  brick(){const G=new THREE.Group(),t=canvasTex(256,128,(g,w,h)=>{g.fillStyle='#c4572f';g.fillRect(0,0,w,h);const r=mulberry32(4);
      for(let i=0;i<500;i++){g.fillStyle=`rgba(${r()<.5?90:230},${r()<.5?30:120},20,${0.08+r()*0.12})`;g.fillRect(r()*w,r()*h,2+r()*3,2+r()*3)}});
    const b=new THREE.Mesh(roundBox(1.8,0.68,0.98,0.05),toyMat(0xffffff,{map:t,roughness:0.85}));G.add(b);
    const hole=new THREE.MeshBasicMaterial({color:0x3a1206});for(const x of[-0.55,0,0.55]){const hh=new THREE.Mesh(new THREE.CylinderGeometry(0.17,0.17,0.02,20),hole);hh.position.set(x,0.345,0);G.add(hh)}
    return G},
  sushi(){const G=new THREE.Group();
    const rice=canvasTex(128,64,(g,w,h)=>{g.fillStyle='#fffdf4';g.fillRect(0,0,w,h);const r=mulberry32(2);for(let i=0;i<90;i++){g.fillStyle=`rgba(200,195,180,${0.3+r()*0.4})`;g.beginPath();g.ellipse(r()*w,r()*h,4,2,r()*3,0,7);g.fill()}});
    const base=new THREE.Mesh(roundBox(1.55,0.42,0.82,0.18),toyMat(0xffffff,{map:rice,roughness:0.8}));base.position.y=-0.13;G.add(base);
    const egg=canvasTex(256,64,(g,w,h)=>{g.fillStyle='#ffd23f';g.fillRect(0,0,w,h);g.fillStyle='rgba(200,120,20,.35)';for(let x=10;x<w;x+=34)g.fillRect(x,0,8,h)});
    const tam=new THREE.Mesh(roundBox(1.8,0.28,0.98,0.1),toyMat(0xffffff,{map:egg,roughness:0.45}));tam.position.y=0.2;G.add(tam);
    const nori=new THREE.Mesh(new THREE.BoxGeometry(0.28,0.74,1.02),toyMat(0x13241a,{roughness:0.6}));nori.position.y=0.0;G.add(nori);
    return G},
  shogi(){const G=new THREE.Group(),sh=new THREE.Shape();
    sh.moveTo(-0.9,-0.46);sh.lineTo(0.42,-0.5);sh.lineTo(0.9,0);sh.lineTo(0.42,0.5);sh.lineTo(-0.9,0.46);sh.lineTo(-0.9,-0.46);
    const geo=new THREE.ExtrudeGeometry(sh,{depth:0.5,bevelEnabled:true,bevelThickness:0.06,bevelSize:0.05,bevelSegments:3});geo.translate(0,0,-0.25);geo.rotateX(-Math.PI/2);
    const wood=canvasTex(256,128,(g,w,h)=>{g.fillStyle='#e8c27a';g.fillRect(0,0,w,h);g.strokeStyle='rgba(150,95,40,.35)';g.lineWidth=2;for(let y=4;y<h;y+=9){g.beginPath();g.moveTo(0,y);g.bezierCurveTo(w*0.3,y+5,w*0.6,y-5,w,y+2);g.stroke()}});
    wood.wrapS=wood.wrapT=THREE.RepeatWrapping;wood.repeat.set(0.6,0.6);
    const p=new THREE.Mesh(geo,toyMat(0xffffff,{map:wood,roughness:0.5}));p.position.y=-0.04;G.add(p);
    const lg=new THREE.PlaneGeometry(0.5,0.92);lg.rotateX(-Math.PI/2);lg.rotateY(Math.PI/2);
    const lt=canvasTex(160,300,(g,w,h)=>{g.clearRect(0,0,w,h);g.fillStyle='#1b1430';g.font="128px 'Yuji Syuku','Yu Mincho','Hiragino Mincho ProN',serif";g.textAlign='center';g.textBaseline='middle';
      g.fillText('王',w/2,h*0.27);g.fillText('将',w/2,h*0.74)});lt.center.set(0.5,0.5);lt.rotation=Math.PI;redraws.push(lt);
    const label=new THREE.Mesh(lg,new THREE.MeshStandardMaterial({map:lt,transparent:true,roughness:0.5}));
    label.position.set(-0.12,0.33,0);G.add(label);
    return G},
  milk(){const G=new THREE.Group();
    const side=canvasTex(320,160,(g,w,h)=>{g.fillStyle='#fff';g.fillRect(0,0,w,h);g.fillStyle='#2f8cff';g.fillRect(0,0,w,18);g.fillRect(0,h-12,w,12);
      g.fillStyle='#1b1430';g.font="800 56px 'M PLUS Rounded 1c',sans-serif";g.textAlign='center';g.textBaseline='middle';g.fillText('牛乳',w*0.36,52);
      // 牛の顔
      const cx=w*0.36,cy=112;g.fillStyle='#fff';g.strokeStyle='#1b1430';g.lineWidth=4;
      g.beginPath();g.ellipse(cx-34,cy-16,10,6,-0.5,0,7);g.ellipse(cx+34,cy-16,10,6,0.5,0,7);g.fill();g.stroke();
      g.beginPath();g.ellipse(cx,cy,30,24,0,0,7);g.fill();g.stroke();g.fillStyle='#1b1430';g.beginPath();g.ellipse(cx-14,cy-10,9,7,0.4,0,7);g.fill();
      g.beginPath();g.arc(cx-9,cy-2,3,0,7);g.arc(cx+9,cy-2,3,0,7);g.fill();
      g.fillStyle='#ffb3c4';g.beginPath();g.ellipse(cx,cy+12,17,10,0,0,7);g.fill();g.stroke();g.fillStyle='#1b1430';g.beginPath();g.arc(cx-6,cy+12,2.4,0,7);g.arc(cx+6,cy+12,2.4,0,7);g.fill();
      g.fillStyle='#ffd23f';g.beginPath();g.moveTo(cx-24,cy-24);g.lineTo(cx-18,cy-36);g.lineTo(cx-14,cy-22);g.moveTo(cx+24,cy-24);g.lineTo(cx+18,cy-36);g.lineTo(cx+14,cy-22);g.fill();
      g.fillStyle='#1b1430';g.font="800 20px 'M PLUS Rounded 1c',sans-serif";g.fillText('200ml',w*0.82,h-34)});redraws.push(side);
    const plain=toyMat(0xffffff,{roughness:0.6}),lab=toyMat(0xffffff,{map:side,roughness:0.6});
    const box=new THREE.Mesh(roundBox(1.35,0.68,0.98,0.04),[plain,plain,plain,plain,lab,lab]);box.position.x=-0.22;G.add(box);
    const tri=new THREE.Shape();tri.moveTo(0,-0.34);tri.lineTo(0.42,0);tri.lineTo(0,0.34);tri.lineTo(0,-0.34);
    const roof=new THREE.Mesh(new THREE.ExtrudeGeometry(tri,{depth:0.96,bevelEnabled:false}),toyMat(0x2f8cff,{roughness:0.5}));roof.position.set(0.45,0,-0.48);G.add(roof);
    const fin=new THREE.Mesh(new THREE.BoxGeometry(0.1,0.72,0.96),toyMat(0x2f8cff,{roughness:0.5}));fin.position.set(0.9,0,0);G.add(fin);
    const straw=new THREE.Mesh(new THREE.CylinderGeometry(0.035,0.035,0.7,10),toyMat(0xff6fa5));straw.position.set(-0.6,0.5,0.2);straw.rotation.z=0.5;G.add(straw);
    return G},
  crown(){const G=new THREE.Group(),gold=toyMat(0xffc928,{roughness:0.22,metalness:0.55,emissive:0x5a3a00}),red=toyMat(0xc21f3a,{roughness:0.7});
    const band=new THREE.Mesh(new THREE.CylinderGeometry(0.46,0.46,0.3,40,1,true),gold);band.material.side=THREE.DoubleSide;band.position.y=-0.18;G.add(band);
    const cap=new THREE.Mesh(new THREE.SphereGeometry(0.44,28,16,0,Math.PI*2,0,Math.PI/2),red);cap.scale.y=0.7;cap.position.y=-0.06;G.add(cap);
    for(let i=0;i<8;i++){const a=i/8*Math.PI*2,sp=new THREE.Mesh(new THREE.ConeGeometry(0.1,0.32,4),gold);sp.position.set(Math.cos(a)*0.43,0.1,Math.sin(a)*0.43);G.add(sp);
      const ball=new THREE.Mesh(new THREE.SphereGeometry(0.05,10,8),gold);ball.position.set(Math.cos(a)*0.43,0.28,Math.sin(a)*0.43);G.add(ball);
      const gem=new THREE.Mesh(new THREE.SphereGeometry(0.055,12,8),toyMat([0xff3355,0x2f8cff,0x3ccf6b,0xa64bff][i%4],{roughness:0.15}));gem.position.set(Math.cos(a)*0.47,-0.18,Math.sin(a)*0.47);G.add(gem)}
    const top=new THREE.Mesh(new THREE.SphereGeometry(0.08,12,10),gold);top.position.y=0.26;G.add(top);
    const crossA=new THREE.Mesh(new THREE.BoxGeometry(0.05,0.2,0.05),gold);crossA.position.y=0.38;G.add(crossA);const crossB=new THREE.Mesh(new THREE.BoxGeometry(0.14,0.05,0.05),gold);crossB.position.y=0.4;G.add(crossB);
    const rim=new THREE.Mesh(new THREE.TorusGeometry(0.47,0.04,8,40),toyMat(0xffffff,{roughness:0.9}));rim.rotation.x=Math.PI/2;rim.position.y=-0.33;G.add(rim);
    G.scale.set(1.5,1,1.05);return G},
  burger(){const G=new THREE.Group();const add=(geo,m,y,sx=1)=>{const o=new THREE.Mesh(geo,m);o.position.y=y;o.scale.x=sx;G.add(o);return o};
    const bun=toyMat(0xe0a050,{roughness:0.45}),sx=1.6;
    add(roundBox(0.95,0.16,0.95,0.07),bun,-0.27,sx);
    add(new THREE.CylinderGeometry(0.5,0.5,0.12,32),toyMat(0x5a2e16,{roughness:0.7}),-0.13,sx);
    const ch=add(new THREE.BoxGeometry(0.86,0.03,0.86),toyMat(0xffc31a,{roughness:0.35}),-0.06,sx);ch.rotation.y=Math.PI/4;
    add(new THREE.CylinderGeometry(0.52,0.5,0.06,14),toyMat(0x6fcf4a,{roughness:0.5}),-0.02,sx);
    add(new THREE.CylinderGeometry(0.44,0.44,0.05,24),toyMat(0xe2453a,{roughness:0.4}),0.03,sx);
    const top=add(new THREE.SphereGeometry(0.5,32,16,0,Math.PI*2,0,Math.PI/2),bun,0.05,sx);top.scale.y=0.62;
    const seed=toyMat(0xfff4d6);const r=mulberry32(7);for(let i=0;i<16;i++){const a=r()*Math.PI*2,rr=0.12+r()*0.3,y=0.05+Math.sqrt(Math.max(0,0.25-rr*rr))*0.62;
      const sd=new THREE.Mesh(new THREE.SphereGeometry(0.03,8,6),seed);sd.scale.set(1.4,0.6,0.8);sd.position.set(Math.cos(a)*rr*sx,y,Math.sin(a)*rr);sd.rotation.y=a;G.add(sd)}
    return G},
  maneki(){const G=new THREE.Group(),wh=toyMat(0xffffff,{roughness:0.35}),red=toyMat(0xe23b3b,{roughness:0.4}),gold=toyMat(0xffc928,{roughness:0.25,metalness:0.5});
    const face=canvasTex(128,128,(g,w,h)=>{g.fillStyle='#fff';g.fillRect(0,0,w,h);g.strokeStyle='#1b1430';g.lineWidth=6;g.lineCap='round';
      g.beginPath();g.arc(40,58,11,Math.PI*1.1,Math.PI*1.9);g.stroke();g.beginPath();g.arc(88,58,11,Math.PI*1.1,Math.PI*1.9);g.stroke();
      g.fillStyle='#ff8fa0';g.beginPath();g.moveTo(58,70);g.lineTo(70,70);g.lineTo(64,77);g.fill();g.lineWidth=3;g.beginPath();g.moveTo(64,77);g.quadraticCurveTo(56,88,48,82);g.moveTo(64,77);g.quadraticCurveTo(72,88,80,82);g.stroke();
      g.lineWidth=2;for(const d of[-1,1])for(const k of[0,1]){g.beginPath();g.moveTo(64+d*24,74+k*7);g.lineTo(64+d*52,70+k*12);g.stroke()}});
    const body=new THREE.Mesh(new THREE.SphereGeometry(0.36,28,20),wh);body.scale.set(1,0.95,1.05);body.position.set(-0.05,-0.05,0);G.add(body);
    const head=new THREE.Mesh(new THREE.SphereGeometry(0.3,28,20),wh);head.position.set(0.05,0.36,0);head.scale.set(0.95,0.88,1.05);G.add(head);
    const fp=new THREE.Mesh(new THREE.SphereGeometry(0.303,24,16,Math.PI-0.95,1.9,Math.PI/2-0.85,1.7),new THREE.MeshStandardMaterial({map:face,roughness:0.35}));fp.position.copy(head.position);fp.scale.copy(head.scale);G.add(fp);
    for(const sz of[-1,1]){const e=new THREE.Mesh(new THREE.ConeGeometry(0.1,0.16,4),wh);e.position.set(0.05,0.6,sz*0.17);e.rotation.x=-sz*0.3;G.add(e);
      const ein=new THREE.Mesh(new THREE.ConeGeometry(0.06,0.1,4),toyMat(0xff9fb0));ein.position.set(0.09,0.59,sz*0.17);ein.rotation.x=-sz*0.3;G.add(ein)}
    const col=new THREE.Mesh(new THREE.TorusGeometry(0.24,0.04,8,30),red);col.rotation.z=Math.PI/2;col.rotation.y=Math.PI/2;col.position.set(0.05,0.12,0);col.rotation.set(Math.PI/2,0,0);G.add(col);
    const bell=new THREE.Mesh(new THREE.SphereGeometry(0.07,14,10),gold);bell.position.set(0.28,0.07,0);G.add(bell);
    const arm=new THREE.Mesh(new THREE.CylinderGeometry(0.07,0.08,0.34,12),wh);arm.position.set(0.12,0.4,-0.24);arm.rotation.x=0.15;G.add(arm);
    const paw=new THREE.Mesh(new THREE.SphereGeometry(0.09,14,10),wh);paw.position.set(0.13,0.58,-0.27);G.add(paw);
    const coin=new THREE.Mesh(new THREE.CylinderGeometry(0.17,0.17,0.04,24),gold);coin.rotation.z=Math.PI/2;coin.position.set(0.3,-0.06,0.18);coin.scale.set(1,1,0.6);G.add(coin);
    for(const[x,z,c]of[[-0.2,0.2,0x1b1430],[-0.25,-0.12,0xff8a1a]]){const p=new THREE.Mesh(new THREE.SphereGeometry(0.1,12,8),toyMat(c));p.scale.y=0.4;p.position.set(x,0.25,z);G.add(p)}
    G.scale.setScalar(1.25);G.position.y=0.02;return G},
  konnyaku(){const G=new THREE.Group(),t=canvasTex(256,128,(g,w,h)=>{g.fillStyle='#8f8b86';g.fillRect(0,0,w,h);const r=mulberry32(21);
      for(let i=0;i<420;i++){g.fillStyle=`rgba(30,28,26,${0.35+r()*0.5})`;g.beginPath();g.arc(r()*w,r()*h,0.8+r()*1.6,0,7);g.fill()}});
    const b=new THREE.Mesh(roundBox(1.72,0.56,0.96,0.16),toyMat(0xffffff,{map:t,roughness:0.12}));b.position.y=-0.06;G.add(b);
    const cut=toyMat(0x77736e,{roughness:0.2});for(const x of[-0.4,0,0.4]){const c=new THREE.Mesh(new THREE.BoxGeometry(0.03,0.02,0.7),cut);c.position.set(x,0.225,0);c.rotation.y=0.6;G.add(c)}
    return G},
  dogeza(){const G=new THREE.Group(),suit=toyMat(0x26324f,{roughness:0.6}),skin=toyMat(0xf3c9a0,{roughness:0.5}),blk=toyMat(0x1b1430,{roughness:0.4}),wht=toyMat(0xffffff);
    const torso=new THREE.Mesh(roundBox(0.78,0.42,0.66,0.16),suit);torso.position.set(-0.02,-0.04,0);torso.rotation.z=-0.28;G.add(torso);
    const hips=new THREE.Mesh(roundBox(0.5,0.46,0.62,0.18),suit);hips.position.set(-0.42,0.0,0);G.add(hips);
    for(const sz of[-1,1]){const leg=new THREE.Mesh(roundBox(0.62,0.2,0.24,0.08),suit);leg.position.set(-0.52,-0.24,sz*0.17);G.add(leg);
      const shoe=new THREE.Mesh(roundBox(0.12,0.16,0.22,0.05),blk);shoe.position.set(-0.86,-0.22,sz*0.17);G.add(shoe);
      const arm=new THREE.Mesh(new THREE.CylinderGeometry(0.075,0.085,0.46,10),suit);arm.position.set(0.42,-0.14,sz*0.27);arm.rotation.z=1.0;G.add(arm);
      const hand=new THREE.Mesh(new THREE.SphereGeometry(0.08,12,8),skin);hand.scale.set(1.3,0.5,1);hand.position.set(0.68,-0.31,sz*0.16);G.add(hand)}
    const collar=new THREE.Mesh(new THREE.TorusGeometry(0.13,0.035,8,20),wht);collar.position.set(0.33,-0.06,0);collar.rotation.y=Math.PI/2;collar.rotation.x=0.4;G.add(collar);
    const head=new THREE.Mesh(new THREE.SphereGeometry(0.19,24,16),skin);head.position.set(0.5,-0.15,0);G.add(head);
    const shine=new THREE.Mesh(new THREE.SphereGeometry(0.06,10,8),toyMat(0xffffff,{transparent:true,opacity:0.6}));shine.scale.set(1,0.4,1.6);shine.position.set(0.47,0.03,0.06);G.add(shine);
    // バーコード（横に流した数本の毛）
    for(let k=0;k<4;k++){const hr=new THREE.Mesh(new THREE.TorusGeometry(0.192,0.008,4,24,Math.PI*0.9),blk);hr.position.set(0.5-0.02*k+0.03,-0.15,0);hr.rotation.set(0,Math.PI/2,0.3);hr.rotation.x=-0.25+k*0.17;G.add(hr)}
    for(const sz of[-1,1]){const side=new THREE.Mesh(new THREE.SphereGeometry(0.07,10,8),blk);side.scale.set(1.3,1,0.5);side.position.set(0.44,-0.16,sz*0.17);G.add(side);
      const lens=new THREE.Mesh(new THREE.TorusGeometry(0.05,0.012,6,16),blk);lens.position.set(0.63,-0.24,sz*0.07);lens.rotation.y=Math.PI/2;G.add(lens);
      const temple=new THREE.Mesh(new THREE.BoxGeometry(0.2,0.012,0.012),blk);temple.position.set(0.55,-0.2,sz*0.185);G.add(temple)}
    const sweat=new THREE.Mesh(new THREE.SphereGeometry(0.045,10,8),toyMat(0x7fd2ff,{roughness:0.1}));sweat.scale.y=1.4;sweat.position.set(0.4,0.1,0.18);G.add(sweat);
    return G},
  pudding(){const G=new THREE.Group();
    const plate=new THREE.Mesh(new THREE.CylinderGeometry(0.62,0.66,0.06,36),toyMat(0xffffff,{roughness:0.25}));plate.scale.x=1.35;plate.position.y=-0.32;G.add(plate);
    const pud=new THREE.Mesh(new THREE.CylinderGeometry(0.3,0.44,0.48,32),toyMat(0xffd977,{roughness:0.3}));pud.scale.x=1.35;pud.position.y=-0.05;G.add(pud);
    const car=new THREE.Mesh(new THREE.CylinderGeometry(0.31,0.32,0.09,32),toyMat(0x7a3d12,{roughness:0.15}));car.scale.x=1.35;car.position.y=0.2;G.add(car);
    for(let i=0;i<7;i++){const a=i/7*Math.PI*2+0.3,d=new THREE.Mesh(new THREE.SphereGeometry(0.05,8,6),toyMat(0x7a3d12,{roughness:0.15}));
      d.scale.set(0.8,1.8,0.8);d.position.set(Math.cos(a)*0.33*1.35,0.13,Math.sin(a)*0.33);G.add(d)}
    const cream=new THREE.Mesh(new THREE.ConeGeometry(0.13,0.18,10),toyMat(0xffffff,{roughness:0.5}));cream.position.y=0.33;G.add(cream);
    const cb=new THREE.Mesh(new THREE.SphereGeometry(0.12,14,10),toyMat(0xffffff,{roughness:0.5}));cb.scale.y=0.6;cb.position.y=0.27;G.add(cb);
    const cherry=new THREE.Mesh(new THREE.SphereGeometry(0.075,14,10),toyMat(0xe2163a,{roughness:0.15}));cherry.position.y=0.45;G.add(cherry);
    const stem=new THREE.Mesh(new THREE.CylinderGeometry(0.01,0.01,0.14,6),toyMat(0x3a8a2a));stem.position.set(0.03,0.54,0);stem.rotation.z=-0.4;G.add(stem);
    return G},
};
function skinModel(m,id){m.models=m.models||{};if(!m.models[id]){const G=MODELS[SKINS[id].model]();G.traverse(o=>{if(o.isMesh){o.castShadow=true;o.receiveShadow=true}});m.g.add(G);m.models[id]=G}return m.models[id]}
// ぷにっと変形（もちもちは大きく揺れる）
const sq=[{v:0,vel:0},{v:0,vel:0}];
// 机の端に止まっている消しゴムは、落ちそうな方向にグラグラ（見た目だけ）
function edgeWobble(e){
  if(e.falling||!isStill(e))return null;let best=9,bd=null;
  for(const[dx,dz]of DIR8)for(let r=0.1;r<=1.0;r+=0.1){if(!inTable(e.x+dx*r,e.z+dz*r)){if(r<best){best=r;bd=[dx,dz]}break}}
  return best<=0.95?[bd[0],bd[1],0.05+0.14*(1-best/0.95)]:null;
}
const _wq=new THREE.Quaternion(),_wa=new THREE.Vector3();
function squash(i,amt){if(!S.e[i])return;sq[i].vel+=amt*(0.3+ETYPES[S.e[i].k].squish);const m=eMesh[i];if(m&&m.jelly&&amt>0.15){m.pw=Math.min(0.3,(m.pw||0)+amt*0.09);m.pt=0}}
// 弾く指
const finger=new THREE.Group();finger.visible=false;scene.add(finger);
{
  const skin=new THREE.MeshStandardMaterial({color:0xe39a72,roughness:0.6});
  const inner=new THREE.Group();inner.rotation.z=-0.28;finger.add(inner);
  const add=(geo,mat,x,y,rz)=>{const m=new THREE.Mesh(geo,mat);m.position.set(x,y,0);if(rz)m.rotation.z=rz;m.castShadow=true;inner.add(m);return m};
  add(new THREE.SphereGeometry(0.3,18,12),skin,0,0);
  add(new THREE.CylinderGeometry(0.3,0.33,1.3,18),skin,-0.65,0,Math.PI/2);
  add(new THREE.SphereGeometry(0.34,18,12),skin,-1.3,0);
  add(new THREE.CylinderGeometry(0.34,0.38,1.6,18),skin,-2.1,0,Math.PI/2);
  add(new THREE.SphereGeometry(0.38,18,12),skin,-2.9,0);
  const nail=add(new THREE.SphereGeometry(0.24,16,8),new THREE.MeshStandardMaterial({color:0xffe6e2,roughness:0.25}),-0.22,0.22);nail.scale.set(1.35,0.35,0.95);
}
let fingerFx={t:-1};
function fingerGap(sub,p){return sub==='power'?0.25+p*1.5:0.55}
function updateFinger(rdt){
  const ph=game.phase,sub=ph==='wait'?game.remoteSub:ph;let show=false,gap=0;
  if(((aiming()&&isMyTurn())||ph==='wait')&&(sub==='dir'||sub==='power')){show=true;gap=fingerGap(sub,game.shot.power)}
  let ox,oz,a=game.shot.angle;
  if(fingerFx.t>=0){fingerFx.t+=rdt;const u=fingerFx.t;show=true;ox=fingerFx.x;oz=fingerFx.z;a=fingerFx.a;
    gap=u<0.04?fingerFx.g0+(-0.25-fingerFx.g0)*(u/0.04):-0.25;if(u>0.5){fingerFx.t=-1;show=false}}
  else{const e=S.e[game.shooter];ox=e.x;oz=e.z}
  finger.visible=show;if(!show)return;
  const dx=Math.cos(a),dz=Math.sin(a),back=EL/2+0.3+gap;
  let j=(sub==='power'&&fingerFx.t<0)?Math.max(0,game.shot.power-0.55)*0.12:0;
  finger.position.set(ox-dx*back+(Math.random()-0.5)*j,0.36,oz-dz*back+(Math.random()-0.5)*j);finger.rotation.y=-a;
}
// 鉛筆・定規
const obsGroup=new THREE.Group();scene.add(obsGroup);let obsMeshes=[];
const PCOL=[0xffc928,0x3cb371,0xe8553e];
const rulerTop=new THREE.MeshStandardMaterial({map:rulerTex,transparent:true,opacity:0.86,roughness:0.15});
const rulerSide=new THREE.MeshStandardMaterial({color:0x8fd3ef,transparent:true,opacity:0.75,roughness:0.15});
function buildObs(os){
  while(obsGroup.children.length)obsGroup.remove(obsGroup.children[0]);
  obsMeshes=os.map(o=>{
    const g=new THREE.Group(),tg=new THREE.Group(),sp=new THREE.Group();g.add(tg);tg.add(sp);
    const add=(geo,mat,x,rot)=>{const m=new THREE.Mesh(geo,mat);m.rotation.z=rot||0;m.position.x=x;m.castShadow=true;m.receiveShadow=true;sp.add(m)};
    const L=o.len,x0=-L/2;
    if(o.kind===0){
      add(new THREE.CylinderGeometry(PR*0.95,PR*0.95,0.18,12),new THREE.MeshStandardMaterial({color:0xff9fb0,roughness:0.9}),x0+0.09,Math.PI/2);
      add(new THREE.CylinderGeometry(PR,PR,0.24,12),new THREE.MeshStandardMaterial({color:0xc9ccd2,metalness:0.7,roughness:0.3}),x0+0.3,Math.PI/2);
      const bl=L-0.42-0.62;add(new THREE.CylinderGeometry(PR,PR,bl,6),new THREE.MeshStandardMaterial({color:PCOL[o.col],roughness:0.5}),x0+0.42+bl/2,Math.PI/2);
      add(new THREE.ConeGeometry(PR,0.62,6),new THREE.MeshStandardMaterial({color:0xe8c79a,roughness:0.9}),L/2-0.31,-Math.PI/2);
      add(new THREE.ConeGeometry(0.075,0.2,8),new THREE.MeshStandardMaterial({color:0x333338,roughness:0.4}),L/2-0.1,-Math.PI/2);
    }else{
      add(new THREE.BoxGeometry(L,RUL_H,RUL_HW*2),[rulerSide,rulerSide,rulerTop,rulerSide,rulerSide,rulerSide],0);
    }
    obsGroup.add(g);return{g,tg,sp};
  });
  syncObs();
}
function syncObs(){
  S.obs.forEach((o,i)=>{const m=obsMeshes[i];if(!m)return;
    m.g.position.set(o.cx,(o.kind===0?PR:RUL_H/2)+o.y,o.cz);m.g.rotation.y=-o.a;m.tg.rotation.z=o.tilt;m.sp.rotation.x=o.roll;});
}
// 予測ドット
// 点は動かさず、道のりに沿って等間隔に置く。濃い色＋白フチで木目に溶けないように
const dotMat=[new THREE.MeshBasicMaterial({color:0xff9a00}),new THREE.MeshBasicMaterial({color:0x2f8cff})];
const dotGeo=new THREE.SphereGeometry(0.1,10,8),dotRim=new THREE.MeshBasicMaterial({color:0xffffff,side:THREE.BackSide});
const DOT_GAP=0.75;
const dots=[];for(let k=0;k<64;k++){const m=new THREE.Mesh(dotGeo,dotMat[0]),r=new THREE.Mesh(dotGeo,dotRim);r.scale.setScalar(1.45);m.add(r);m.visible=false;scene.add(m);dots.push(m)}
// 先端（止まる所）の印：白フチの円
const tipMark=new THREE.Group();{const rim=new THREE.Mesh(new THREE.CircleGeometry(0.42,32),new THREE.MeshBasicMaterial({color:0xffffff,transparent:true,opacity:0.95,depthWrite:false}));
  const ctr=new THREE.Mesh(new THREE.CircleGeometry(0.3,32),dotMat[0]);ctr.position.z=0.002;rim.add(ctr);rim.rotation.x=-Math.PI/2;tipMark.add(rim);tipMark.userData.ctr=ctr}
tipMark.visible=false;scene.add(tipMark);
const arrowHead=new THREE.Mesh(new THREE.ConeGeometry(0.22,0.5,12),dotMat[0]);arrowHead.visible=false;scene.add(arrowHead);
// 消しカス
const parts=[];const pGeo=new THREE.BoxGeometry(0.12,0.06,0.09);
const pMatE=new THREE.MeshStandardMaterial({color:0xeeeeea,roughness:1});
const pMatW=new THREE.MeshStandardMaterial({color:0xe2b77a,roughness:1});
function spawn(x,y,z,n,mat,spd){
  for(let k=0;k<n;k++){
    let p=parts.find(q=>!q.alive);
    if(!p){if(parts.length>=180)break;const m=new THREE.Mesh(pGeo,mat);scene.add(m);p={m};parts.push(p)}
    p.alive=true;p.m.material=mat;p.m.visible=true;p.life=4+Math.random()*3;p.m.position.set(x,y,z);
    const a=Math.random()*Math.PI*2,s=spd*(0.3+Math.random());p.vx=Math.cos(a)*s;p.vz=Math.sin(a)*s;p.vy=2+Math.random()*spd*0.8;p.m.rotation.set(Math.random()*3,Math.random()*3,0);
  }
}
function updateParts(dt){
  for(const p of parts){if(!p.alive)continue;const m=p.m;
    p.vy-=20*dt;m.position.x+=p.vx*dt;m.position.y+=p.vy*dt;m.position.z+=p.vz*dt;
    if(m.position.y<0.03&&p.vy<0&&inTable(m.position.x,m.position.z)){m.position.y=0.03;p.vy=0;p.vx*=0.6;p.vz*=0.6}
    p.life-=dt;if(p.life<=0||m.position.y<FLOOR){p.alive=false;m.visible=false}
  }
}
function clearParts(){parts.forEach(p=>{p.alive=false;p.m.visible=false})}

// ================= ゲーム状態 =================
const game={mode:'cpu',me:0,diff:1,myType:0,types:[0,0],pickFor:'cpu',seed:1,round:1,score:[0,0],shooter:0,phase:'title',token:0,
  shot:{type:0,angle:0,curve:1,power:0},remoteSub:'select',cpuAnim:null,gaugeT:0,flyT:0,realT:0,
  pendingShot:null,pendingSettle:null,waitSettle:false,againMe:false,againRemote:false};
setStage(0);
let S=newState(12345);buildObs(S.obs);
let acc=0,slowT=0,hitstop=0,shake=0,speedFx=0,camTarget=0,fallCam=null,keys={},holdDir=0,drag=null,aimSendT=0;
const cam={pos:new THREE.Vector3(18,9,14),look:new THREE.Vector3(),dirA:0,fov:60};

const later=(fn,ms)=>{const tk=game.token;setTimeout(()=>{if(tk===game.token)fn()},ms)};
const myIdx=()=>game.mode==='cpu'?0:game.me;
const isMyTurn=()=>game.shooter===myIdx();
const aiming=()=>['dir','power'].includes(game.phase);

function toast(t,ms=2600,prio=0){const el=$('toast'),now=performance.now();if(prio<(toast.p||0)&&now<(toast.until||0))return;toast.p=prio;toast.until=now+ms;
  el.textContent=t;el.classList.toggle('big',prio>0);el.classList.remove('hidden');clearTimeout(toast.t);toast.t=setTimeout(()=>{el.classList.add('hidden');toast.p=0},ms)}
function pop(text,cls){const el=$('pop');el.textContent=text;el.className='';void el.offsetWidth;el.className='show '+cls}
function showScreen(id){if(id==='pickMenu'){pickSel=null;pickRender()}['title','rankName','rankLobby','rankGacha','rankDress','rankQueue','rankVs','rankBoard','pickMenu','netMenu','howto','result','challenge'].forEach(s=>$(s).classList.toggle('hidden',s!==id))}
function showPanel(id){['pAim','pWait'].forEach(p=>$(p).classList.toggle('hidden',p!==id))}
function updateHUD(){
  const names=game.mode==='cpu'?['あなた',GT()?GT().st.name:'CPU']:(game.me===0?['あなた','ライバル']:['ライバル','あなた']);
  if(game.ranked){names[game.me]=RK.name;names[1-game.me]=game.ranked.opp.name}
  $('nm0').textContent=names[0];$('nm1').textContent=names[1];
  for(let i=0;i<2;i++){$('ty'+i).textContent=ETYPES[game.types[i]].short;const t=TITLES[titleOf(i)];$('tl'+i).textContent=t?t.name:''}
  for(let i=0;i<2;i++)$('st'+i).textContent='★'.repeat(game.score[i])+'☆'.repeat(Math.max(0,game.need-game.score[i]));
  $('round').textContent=GT()?GT().n+'人目':'ROUND '+game.round;
}
function setTurnText(){
  const t=$('turn');
  if(isMyTurn()){t.textContent='あなたのターン！';t.style.color=game.shooter?'#9fd8ff':'#ffd23f'}
  else{t.textContent=(game.ranked?game.ranked.opp.name:game.mode==='cpu'?(GT()?GT().st.name:'CPU'):'ライバル')+'のターン';t.style.color='#fff'}
}

// ===== 勝ち抜き戦（全員1本勝負。5の倍数ごとに強敵。負けたら1人目から） =====
const GT_NAMES=['新入生','となりの席の子','日直','給食当番','図書委員','放送委員','飼育係','黒板消し係','前の席の子','保健委員','転校生','帰宅部エース','体育委員','学級委員','ツルピカ先輩','もち委員長','掃除当番','忘れ物王'];
const GT_BOSSES=[{name:'激落王',k:3},{name:'生徒会長',k:5},{name:'教頭先生',k:1},{name:'校長先生',k:3}];
const lerp=(a,b,t)=>a+(b-a)*t;
function stageOf(n){
  if(n%5===0){const i=n/5-1,B=GT_BOSSES[i%GT_BOSSES.length];
    return{name:(i>=GT_BOSSES.length?'真・':'')+B.name,k:B.k,need:1,boss:true,cfg:{n:360,na:0.012,np:0.015,refine:true}}}
  if(n===1)return{name:GT_NAMES[0],k:0,need:1,easy:true,cfg:{n:60,easy:true}};   // 1人目は必ず落とせる練習相手
  const t=Math.min(1,(n-1)/13),fixed=[0,1,2,4];   // 最初の4人は消しゴムの種類を順番に見せる
  return{name:GT_NAMES[(n-1-Math.floor(n/5))%GT_NAMES.length],k:n<=4?fixed[n-1]:randType(),need:1,
    cfg:{n:Math.round(lerp(40,300,t)),na:lerp(0.2,0.02,t),np:lerp(0.16,0.022,t)}}}
const GT=()=>game.mode==='cpu'&&!game.ranked?game.gt:null,cpuName=()=>GT()?GT().st.name:'CPU';
let gtBest=0;try{gtBest=+SAVE.getItem('gekiochiBest')||0}catch(e){}
function gtBestText(){$('bestTxt').textContent=gtBest?'自己ベスト：'+gtBest+'人激落':'どこまで勝ち抜ける？'}
const allInv=()=>{const a=rkInv();UNL.forEach(x=>{if(PRIZES[x]&&!a.includes(x))a.push(x)});return a};
// ボスを倒すと解放されるもの
const GT_REWARDS={5:{id:'t10',name:'称号「激落王を倒した者」'},10:{id:'e3',name:'おうごん消しゴム'},15:{id:'t11',name:'称号「勝ち抜きの鬼」'},20:{id:'x7',name:'スキン「王冠」'}};
function gtReward(n){const R=GT_REWARDS[n];if(!R||!unlock(R.id))return;
  later(()=>{toast('🎉 解放！ '+R.name+(R.id==='e3'?'\n消しゴム選択で使えるよ':'\nきせかえで使えるよ'),4200,1);SFX.max()},1500)}
function gtRecord(wins){if(wins<=gtBest)return false;gtBest=wins;try{SAVE.setItem('gekiochiBest',wins)}catch(e){}gtBestText();return true}
function gtGo(n,keep,cont){if(n===1)stat('gt_start');game.oppSkin=game.oppTitle='';const st=stageOf(n);game.gt={n,st,won:false,cont:!!cont};game.me=0;game.ranked=null;startMatch('cpu',(Math.random()*1e9)|0,0,[game.myType,st.k],st.need,keep)}
function startMatch(mode,seed,first,types,need,keepBgm){
  {const g=mode==='cpu'&&!game.ranked?game.gt:null;setStage(g?(g.n-1)%3:((seed>>>0)%3));}
  if(mode==='net'&&!game.ranked)stat('net_start');
  stat('pick_'+(mode==='net'?types[game.me]:types[0]));
  bgmPlay('battle',!keepBgm);game.need=need||2;
  game.turnLimit=(mode==='net'||game.ranked)?TURN_SEC:0;
  game.token++;game.mode=mode;game.seed=seed;game.types=types.slice();applyLooks(game.types);game.score=[0,0];game.round=1;
  game.pendingShot=null;game.pendingSettle=null;game.waitSettle=false;game.againMe=game.againRemote=false;
  showScreen(null);$('hud').classList.remove('hidden');
  startRound(first);
}
function startRound(first){
  S=newState(game.seed+game.round*7919,game.types);buildObs(S.obs);
  {const g=GT();if(g&&g.st.easy){const o=S.e[1];o.m*=0.5;o.mu*=0.75}}   // 練習相手は軽くてよく滑るclearParts();fallCam=null;sq.forEach(q=>{q.v=0;q.vel=0});
  game.shooter=first;game.phase='between';updateHUD();$('turn').textContent='';showPanel(null);
  const g=GT();pop(g&&game.round===1?(g.st.boss?'強敵出現！！':g.n+'人目！'):'ROUND '+game.round,'mid');if(game.round===1)toast('ステージ：'+STAGE_NAMES[game.stage]);SFX.round();if(game.round>1)bgmHit('crash');
  later(beginTurn,game.round===1?900:700);
}
const TURN_SEC=20;
function beginTurn(){
  game.turnEnd=Date.now()+TURN_SEC*1000;game.lastTick=-1;
  const me=S.e[game.shooter],op=S.e[1-game.shooter];
  game.shot={type:0,angle:Math.atan2(op.z-me.z,op.x-me.x),curve:1,power:0};
  me.yaw=game.shot.angle;camTarget=game.shooter;fallCam=null;
  cam.dirA=game.shot.angle;setTurnText();
  if(isMyTurn()){game.phase='dir';game.kbCharge=false;drag=null;applyShotMode(false);setAimHint();showPanel('pAim')}
  else{
    game.phase='wait';game.remoteSub='select';
    if(game.mode==='cpu'){const hb=!!game.ranked;   // ランクマの相手は人と同じ見え方・間合いで
      $('waitText').textContent=hb?'ライバルが狙っている…（打ち方をえらび中）':cpuName()+' 考え中…';showPanel('pWait');
      later(()=>{const sh=cpuChoose(S,game.shooter,GT()?GT().st.cfg:game.diff);game.cpuAnim={sh,t:0,a0:game.shot.angle,k:hb?1.6+Math.random()*0.8:1};game.shot.type=sh.type;game.shot.curve=sh.curve;
        $('waitText').textContent=hb?'ライバルが狙っている…（'+TYPE_NAMES[sh.type]+'）':cpuName()+'：'+TYPE_NAMES[sh.type]+'で狙っている…'},hb?1500+Math.random()*3500:450)}
    else{$('waitText').textContent='ライバルが狙っている…';showPanel('pWait');if(game.pendingShot){const m=game.pendingShot;game.pendingShot=null;later(()=>m.pass?passTurn():fireShot(m),300)}}
  }
}
// 打ち方は1つのボタンで「ストレート→ループ→カーブ↪→カーブ↩」と切り替え（次のターンも引き継ぐ）
const SHOT_MODES=[{type:0,curve:1,name:'ストレート'},{type:1,curve:1,name:'ループ'},{type:2,curve:1,name:'カーブ↪'},{type:2,curve:-1,name:'カーブ↩'}];
let shotMode=0;try{shotMode=clamp(+SAVE.getItem('gekiochiShot')||0,0,3)}catch(e){}
function applyShotMode(anim){const m=SHOT_MODES[shotMode];game.shot.type=m.type;game.shot.curve=m.curve;
  document.querySelectorAll('#typeRow button').forEach((b,i)=>{b.className=i===shotMode?'on':'';if(anim&&i===shotMode){void b.offsetWidth;b.classList.add('pulse')}});
  try{SAVE.setItem('gekiochiShot',shotMode)}catch(e){}}
function cycleShot(){if(!isMyTurn()||!aiming())return;shotMode=(shotMode+1)%SHOT_MODES.length;applyShotMode(true);SFX.click()}
function setShotMode(i){if(!isMyTurn()||!aiming())return;shotMode=i;applyShotMode(true);SFX.click()}
// 互換用（撮影スクリプトなどから呼ばれる）
function chooseType(t){shotMode=t===2?(game.shot.curve<0?3:2):t;applyShotMode(false)}
function setCurve(c){if(game.shot.type!==2)return;shotMode=c<0?3:2;applyShotMode(false)}
function toPower(){if(!isMyTurn()||!aiming())return;game.phase='power';game.kbCharge=true;game.shot.power=0;chargeStart()}
function back(){}
function curveLabel(){}
// 引っぱって弾く：左右で向き、下に引っぱるとパワー、離すと発射
const PULL_MAX=()=>Math.min(innerWidth,innerHeight)*0.36;
// ===== 指のお手本（弾けた回数が2回になるまで、自分の番に出す） =====
const TUT={n:0};try{TUT.n=+SAVE.getItem('gekiochiTut')||0}catch(e){}
function tutCount(){TUT.n++;try{SAVE.setItem('gekiochiTut',TUT.n)}catch(e){}}
const _tv=new THREE.Vector3();
function tutUpdate(){const el=$('ghost');
  const on=TUT.n<2&&game.phase==='dir'&&isMyTurn()&&!drag&&!game.kbCharge&&matchMedia('(pointer:coarse)').matches;
  el.classList.toggle('hidden',!on);if(!on){TUT.t0=null;return}
  if(TUT.t0==null)TUT.t0=game.realT;
  // 画面のどこからでもなぞれるので、お手本は見やすい画面の真ん中で見せる
  const ex=innerWidth/2,ey=innerHeight*0.36,P=PULL_MAX(),T=(game.realT-TUT.t0)%3.6,f=$('ghostF'),cap=$('ghostCap');
  let x=ex,y=ey+46,press=false,txt;
  if(T<1.5){x=ex+Math.sin(T/1.5*Math.PI*2)*Math.min(90,innerWidth*0.2);press=true;txt='① 左右になぞって 向きを決める'}
  else if(T<3.0){const u=Math.min(1,(T-1.5)/1.1),k=1-(1-u)*(1-u);y=ey+46+P*0.75*k;press=true;txt='② 下に引っぱって…'}
  else{y=ey+46+P*0.75;txt='③ 指をはなすと 弾く！'}
  f.style.transform=`translate(${x}px,${y}px) scale(${press?0.92:1.08})`;f.classList.toggle('up',!press);
  $('ghostLine').style.cssText=T>=1.5&&T<3.0?`left:${ex}px;top:${ey+46}px;height:${Math.max(0,y-ey-46)}px;opacity:1`:'opacity:0';
  cap.textContent=txt;cap.style.top=Math.max(70,ey-110)+'px'}
function aimStart(x,y){if(!isMyTurn()||!aiming()||game.kbCharge)return false;drag={x0:x,y0:y,x,y,lx:x,mode:null};return true}
// 1回のなぞりは「向き」か「引っぱり」のどちらか一方だけ（最初の動きで決める）
const AIM_GAIN=()=>Math.min(0.0032,1.3/innerWidth);
function aimMove(x,y){
  if(!drag||!isMyTurn()||!aiming())return;
  drag.x=x;drag.y=y;
  if(!drag.mode){const dx=x-drag.x0,dy=y-drag.y0;if(Math.hypot(dx,dy)<12)return;
    drag.mode=dy>0&&dy>Math.abs(dx)*0.8?'pull':'aim';drag.lx=drag.mode==='aim'?drag.x0:x}
  // 引っぱり中も左右で微調整できる（感度は向き合わせの35%）
  game.shot.angle+=(x-drag.lx)*AIM_GAIN()*(drag.mode==='aim'?1:0.35);drag.lx=x;
  if(drag.mode==='aim')return;
  const p=Math.min(1,Math.max(0,y-drag.y0)/PULL_MAX());
  if(p>0.05){if(game.phase!=='power'){game.phase='power';chargeStart()}const pp=game.shot.power;game.shot.power=p;chargeSet(p);if(pp<0.96&&p>=0.96)SFX.max()}
  else if(game.phase==='power'){game.phase='dir';game.shot.power=0;chargeStop()}
}
function aimEnd(){
  if(!drag)return;drag=null;
  if(game.phase==='power'&&isMyTurn()&&game.shot.power>=0.08){myFire();return}
  if(game.phase==='power'){chargeStop();game.phase='dir'}game.shot.power=0;
}
function setAimHint(){const t=matchMedia('(pointer:coarse)').matches?'左右になぞって向き → 下に引っぱって離すと弾く！':'←→で向き ／ スペース長押し→離すと弾く！（ドラッグでもOK）';$('aimHint').textContent=t}
function myFire(){
  if(game.phase!=='power'||!isMyTurn())return;stat('shot1',true);tutCount();drag=null;game.kbCharge=false;
  // 予測線と同じ丸め方で打つ（見えている線どおりに飛ぶ）
  const sh={type:game.shot.type,angle:+(+game.shot.angle).toFixed(3),curve:game.shot.curve,power:+(+game.shot.power).toFixed(2)};
  if(game.mode==='net')netSend(Object.assign({t:'shot'},sh));
  fireShot(sh);
}
function fireShot(sh){
  game.shot={type:sh.type,angle:sh.angle,curve:sh.curve,power:sh.power};
  launch(S,game.shooter,game.shot);game.phase='flying';game.flyT=0;acc=0;game.ff=false;camTarget=game.shooter;fallCam=null;
  showPanel(null);$('gauge').classList.add('hidden');$('turn').textContent='';
  chargeStop();SFX.flick(sh.power);if(sh.power>0.6)bgmHit('crash');if(sh.type===1)SFX.jump();
  const e=S.e[game.shooter],bx=e.x-Math.cos(sh.angle)*0.9,bz=e.z-Math.sin(sh.angle)*0.9;
  fingerFx={t:0,g0:fingerGap('power',sh.power),x:e.x,z:e.z,a:sh.angle};
  hitstop=0.08+sh.power*0.06;shake=0.5+sh.power*0.8;cam.fov+=6+sh.power*12;
  startBurst(bx,0.35,bz,sh.power);squash(game.shooter,1.2+sh.power*1.5);
  pop(sh.power>0.93?'MAX!! バチィン！！':sh.power>0.6?'バチィン！！':'ペチッ！','small');
  spawn(bx,0.3,bz,6+(sh.power*10|0),pMatE,2+sh.power*3);
}
// 時間切れ：その手はパスして相手の番へ
function passTurn(){
  chargeStop();drag=null;game.kbCharge=false;game.cpuAnim=null;game.phase='between';showPanel(null);
  pop('時間切れ！','mid');SFX.buzz();game.shooter=1-game.shooter;later(beginTurn,1200);
}
function doTimeout(){if(!isMyTurn()||!aiming())return;if(game.mode==='net')netSend({t:'pass'});passTurn()}
function opponentStalled(){
  if(game.phase!=='wait'||isMyTurn()||game.mode!=='net')return;
  netSend({t:'stallwin'});toast('相手の反応がありません。あなたの勝ち！');endMatch(myIdx());
}
function updateTimer(){
  const lim=game.turnLimit,el=$('tmr');
  const on=lim&&(aiming()||game.phase==='wait')&&!(game.mode==='cpu'&&!isMyTurn()&&!game.ranked);
  if(!on){if(!el.classList.contains('hidden'))el.classList.add('hidden');return}
  el.classList.remove('hidden');
  const rem=(game.turnEnd-Date.now())/1000,sec=Math.max(0,Math.ceil(rem));
  $('tmrN').textContent=sec;el.style.setProperty('--p',clamp(rem/lim,0,1));
  el.style.setProperty('--c',rem<=5?'#ff3b2f':rem<=10?'#ffd23f':'#3ad06b');el.classList.toggle('hot',rem<=5);
  if(isMyTurn()&&sec<=5&&sec>0&&sec!==game.lastTick){game.lastTick=sec;SFX.tick()}
  if(rem<=0&&isMyTurn()&&aiming())doTimeout();
  else if(rem<=-10&&!isMyTurn())opponentStalled();
}
function onSettled(){
  game.phase='settling';
  if(game.mode==='net'&&game.me!==0){game.waitSettle=true;return}
  if(game.mode==='net')netSend({t:'settle',st:serState(S)});
  later(resolveTurn,350);
}
function resolveTurn(){
  const f0=S.e[0].fell,f1=S.e[1].fell;
  if(!f0&&!f1){
    // 端っこで止まったら：自分なら「ギリギリ！！」、相手なら「おしい！！」
    const me=myIdx(),nm=!!edgeWobble(S.e[me]),no=!!edgeWobble(S.e[1-me]);
    const msg=nm&&no?(game.shooter===me?'おしい！！':'ギリギリ！！'):no?'おしい！！':nm?'ギリギリ！！':null;
    if(msg){pop(msg,'mid');SFX.creak()}
    game.shooter=1-game.shooter;game.phase='between';later(beginTurn,msg?1100:250);return}
  const gE=GT();
  // 1人目（練習相手）は自分が落ちてもセーフ。机に戻してもう一回
  if(gE&&gE.st.easy&&f0&&!f1){const o=S.e[1],e=mkE(-START_X,0,0,S.e[0].k);if(Math.hypot(o.x-e.x,o.z-e.z)<1.6)e.z=o.z>0?-1.8:1.8;
    e.yaw=Math.atan2(o.z-e.z,o.x-e.x);S.e[0]=e;fallCam=null;camTarget=0;pop('セーフ！もう一回！','mid');SFX.max();
    game.shooter=0;game.phase='between';later(beginTurn,1300);return}
  let w=-1;if(f0&&!f1)w=1;else if(f1&&!f0)w=0;else if(gE&&gE.st.easy)w=0;
  game.phase='between';let next;
  if(w<0){pop('相打ち！！','mid');next=1-game.shooter}
  else{game.score[w]++;updateHUD();pop(w===myIdx()?'ナイス激落！':'落とされた…','mid');next=1-w}
  if(w>=0&&game.score[w]>=game.need){const g=GT();
    // 勝ち抜き中に勝ったら、結果画面をはさまずに次の相手へ
    if(g&&w===myIdx()){if(g.n<=5)stat('gt_win'+g.n);chalCheck(g.n);if(g.st.boss){later(()=>pop('強敵撃破！！','mid'),1000);gtReward(g.n)}
      later(()=>{const r=(!g.cont&&gtRecord(g.n))||g.rec;gtGo(g.n+1,true,g.cont);game.gt.rec=r},g.st.boss?2300:1500)}
    else later(()=>endMatch(w),1700)}
  else later(()=>{game.round++;startRound(next)},1500);
}
function endMatch(w){
  game.token++;chargeStop();if(game.ranked)stat('rank_end');
  if(game.mode==='net'&&!(game.ranked&&game.ranked.bot))stat((w===myIdx()?'vsw_':'vsl_')+game.types[myIdx()]);
  game.phase='over';$('hud').classList.add('hidden');showScreen('result');
  const mine=w===myIdx();$('resT').textContent=mine?'YOU WIN!!':'YOU LOSE…';
  $('resS').textContent=`${game.score[myIdx()]} － ${game.score[1-myIdx()]}`;
  $('bAgain').textContent=game.ranked?'もう一回ランクマッチ':'もう一回！';$('bAgain').disabled=false;
  $('bRetry').classList.add('hidden');
  const g=GT();if(g){g.won=mine;if(!mine)stat('gt_lose'+Math.min(g.n,6));const wins=mine?g.n:g.n-1,rec=(!g.cont&&gtRecord(wins))||(!mine&&g.rec);
    if(!mine&&g.st.boss)$('bRetry').classList.remove('hidden');
    $('resT').textContent=wins+'人激落！';
    $('resS').textContent=g.n+'人目で敗退\n相手：'+g.st.name;$('bAgain').textContent='1人目からもう一回'
    if(rec)$('resS').textContent+='\n自己ベスト更新！';const c=game.chal;if(c)$('resS').textContent+=wins>c.n?`\n${c.name}の${c.n}人を超えた！`:`\n${c.name}の記録まで あと${c.n-wins+1}人`;if(g.cont)$('resS').textContent+='\n（再挑戦中は記録に入りません）'}
  $('resRate').classList.add('hidden');if(game.ranked)rkReportEnd(mine);
  setShare(mine);
  bgmPlay(null);const gw=GT();(gw?gw.n>1:mine)?SFX.win():SFX.lose();
  setTimeout(()=>{if(game.phase==='over')bgmPlay('menu')},2600);
}
// 結果の共有（スマホは共有シート、それ以外はXの投稿画面）
const GAME_URL='https://zirihinit.github.io/gekiochi/?v=2',GAME_TAG='激落消しゴムバトル';
let shareData=null,shareNative=!!navigator.share;
function setShare(mine){
  const me=myIdx(),sc=`${game.score[me]}-${game.score[1-me]}`,et=ETYPES[game.types[me]].name;let text;
  if(game.ranked){const g=game.ranked,K=g.K||RK_K,E=g.E==null?0.5:g.E,pre=g.pre==null?rkRating():g.pre;
    const r=Math.round(pre+(mine?K*(1-E):-K*E)),t=tierOf(r).name;
    text=mine?`ランクマッチで${sc}で激落勝ち！ レート${r}（${t}）`:`ランクマッチで${sc}で激落させられた… レート${r}（${t}）`}
  else if(game.mode==='cpu'){const g=game.gt||{n:1},wins=mine?g.n:g.n-1;
    text=wins?`勝ち抜き戦で${wins}人激落させた！（${et}${g.cont?'・再挑戦あり':''}）`:`勝ち抜き戦、1人目で激落させられた…`}
  else text=mine?`ネット対戦でライバルを${sc}で激落させた！`:`ネット対戦でライバルに${sc}で激落させられた…`;
  // 勝ち抜き戦で1人以上倒したら「挑戦状リンク」にする（踏んだ人はそのまま勝ち抜き戦に入れる）
  let url=GAME_URL,chal=false;
  if(game.mode==='cpu'&&!game.ranked){const g=game.gt||{n:1},wins=mine?g.n:g.n-1;
    if(wins>0){chal=true;url=chalURL(wins,game.types[me]);const c=game.chal;
      text=(c&&wins>c.n?`${c.name}の${c.n}人を超えて、勝ち抜き戦で${wins}人激落させた！`:`勝ち抜き戦で${wins}人激落させた！（${et}）`)+'\nこの記録、超えられる？👇'}}
  text='「激落！！消しゴムバトル！！」'+text;
  shareData={text,url};
  // 本文・URL・ハッシュタグを改行で区切って、すべて本文に入れる（url/hashtagsを分けるとXが空白でつなげてしまう）
  $('bShare').href='https://x.com/intent/post?text='+encodeURIComponent(text+'\n'+url+'\n#'+GAME_TAG);
  $('bShare').textContent=chal?'Xに挑戦状をポスト':'結果をポストする';
  $('bShareLine').classList.toggle('hidden',!chal);
  $('bShareLine').href='https://line.me/R/share?text='+encodeURIComponent(text+'\n'+url);
}
function toTitle(){
  setStage(0);
  bgmPlay('menu');gachaBadge();
  game.token++;game.phase='title';chargeStop();game.ranked=null;game.gt=null;rkCleanupQueue();netClose();$('hud').classList.add('hidden');showScreen('title');
  S=newState(12345);buildObs(S.obs);applyLooks([0,0]);clearParts();
}
function handleEvents(ev){
  for(const e of ev){
    if(e.k==='hit'){if(e.p<1)continue;SFX.hit(e.p);if(e.mochi)SFX.boing(e.p);if(e.slick)SFX.flick(0.25);if(e.buttobi)SFX.boing(e.p*0.6);spawn(e.x,e.y+0.5,e.z,Math.min(24,(e.p*2)|0),pMatE,2+e.p*0.3);
      const am=Math.min(3.2,e.p*0.2),vi=e.vic|0;squash(vi,am*1.5);squash(1-vi,am*0.4);eMesh[vi].vib=Math.min(0.22,0.05+e.p*0.012);
      if(e.p>5){hitstop=0.04+Math.min(0.09,e.p*0.006);shake=Math.min(1.2,e.p*0.09);pop(e.buttobi?'ブッとび！！':e.slick?'ツルッ！！':e.mochi?'ボヨーン！！':e.p>11?'ドカーン！！':e.p>8?'バシッ！！':'パシッ！','small')}}
    else if(e.k==='obs'){if(e.p<0.8)continue;e.kind===0?SFX.pencil(e.p):SFX.ruler(e.p);squash(e.i,Math.min(2.5,e.p*0.14));
      spawn(e.x,0.35,e.z,Math.min(8,(e.p)|0),e.kind===0?pMatW:pMatE,2);shake=Math.max(shake,Math.min(0.5,e.p*0.05));
      if(e.p>7)pop(e.kind===0?'カキーン！':'パコーン！','small')}
    else if(e.k==='oo'){if(e.p>1.2)SFX.pencil(e.p*0.5)}
    else if(e.k==='ofall'){SFX.drop();if(e.kind===1)pop('定規が落ちた！','small')}
    else if(e.k==='ofloor'){SFX.clack()}
    else if(e.k==='land'){squash(e.i,Math.min(2.5,e.p*0.12));if(e.p>3){SFX.land(e.p);spawn(e.x,0.1,e.z,4,pMatE,2);shake=Math.max(shake,0.2)}}
    else if(e.k==='fall'){const eFz=GT()&&GT().st.easy&&e.i===0;SFX.fall();bgmHit('boom');slowT=eFz?0.6:1.5;pop(eFz?'あっ！':'激落！！','big');shake=0.6;camTarget=e.i;
      const c=nearestOnTable(e.x,e.z),ex=c[0],ez=c[1];let ix=e.x-ex,iz=e.z-ez,l=Math.hypot(ix,iz);if(l<1e-6){ix=ex;iz=ez;l=Math.hypot(ix,iz)||1}
      fallCam={pos:new THREE.Vector3(ex-ix/l*3.4,3.6,ez-iz/l*3.4)}}
    else if(e.k==='floor'){SFX.floor()}
  }
}

// ================= ネット対戦 (PeerJS) =================
const net={peer:null,conn:null};
function netStatus(h){$('netStatus').innerHTML=h}
function netSend(o){if(net.conn&&net.conn.open)try{net.conn.send(o)}catch(e){}}
function netClose(){invShow(null);game.oppSkin=game.oppTitle='';const c=net.conn,p=net.peer;net.conn=null;net.peer=null;try{c&&c.close()}catch(e){}try{p&&p.destroy()}catch(e){}}
function setupConn(c){
  c.on('data',onNet);
  c.on('close',()=>{
    if(net.conn!==c)return;
    if(game.ranked&&!game.ranked.done&&game.phase!=='over'&&game.phase!=='title'){
      if(isMyTurn()&&game.turnLimit&&Date.now()>game.turnEnd+5000){toast('時間切れのまま接続が切れたため負けになりました');endMatch(1-myIdx());return}
      toast('相手が切断しました。あなたの勝ち！');endMatch(myIdx());return}
    if(game.ranked)return;
    if(RK.q&&game.phase==='title'){rkQueueFail('相手との接続が切れました');return}
    if(game.mode==='net'&&game.phase!=='title'){toast('相手との接続が切れました');toTitle()}});
}
function netHost(){stat('net_host');
  netClose();if(!window.Peer){netStatus('通信ライブラリを読み込めませんでした');return}
  const code=String(1000+Math.floor(Math.random()*9000));game.me=0;
  netStatus('部屋を作成中…');
  const peer=new Peer(PEER_PFX+code);net.peer=peer;
  peer.on('open',()=>{netStatus(`部屋コード<br><span class="code">${code}</span><br>コードか招待リンクを送ってね。待機中…`);invShow(code)});
  peer.on('connection',c=>{
    if(net.conn){c.close();return}net.conn=c;
    c.on('open',()=>{invShow(null);setupConn(c);netStatus('相手が来た！準備中…')});
  });
  peer.on('error',e=>{if(e.type==='unavailable-id'){netHost()}else netStatus('エラー：'+e.type)});
}
function netJoin(){stat('net_join');
  const code=$('codeIn').value.trim();
  if(!/^\d{4}$/.test(code)){netStatus('4ケタの数字を入れてね');return}
  netClose();if(!window.Peer){netStatus('通信ライブラリを読み込めませんでした');return}
  game.me=1;netStatus('接続中…');
  const peer=new Peer();net.peer=peer;
  peer.on('open',()=>{const c=peer.connect(PEER_PFX+code,{reliable:true});net.conn=c;c.on('open',()=>{setupConn(c);netStatus('接続しました！');netSend({t:'hello',k:game.myType,sk:MY.skin,ti:MY.title})})});
  peer.on('error',e=>netStatus(e.type==='peer-unavailable'?'部屋が見つかりません…<br>コードを確認してね':'エラー：'+e.type));
}
function onNet(m){
  if(!m||!m.t)return;
  if(m.t==='hello'&&m.rk){rkOnHello(m);return}
  if(m.t==='start'&&m.rk){rkOnStart(m);return}
  if(m.t==='hello'){if(game.me!==0||game.phase!=='title'||RK.q)return;const types=[game.myType,safeType(m.k)],seed=(Math.random()*1e9)|0;
    game.oppSkin=m.sk;game.oppTitle=m.ti;netSend({t:'start',seed,first:0,types,sk:MY.skin,ti:MY.title});startMatch('net',seed,0,types)}
  else if(m.t==='start'){game.me=1;if('sk' in m){game.oppSkin=m.sk;game.oppTitle=m.ti}startMatch('net',m.seed,m.first,m.types||[0,0])}
  else if(m.t==='aim'){if(game.phase==='wait'&&!isMyTurn()){Object.assign(game.shot,{type:m.type,angle:m.angle,curve:m.curve,power:m.power});game.remoteSub=m.sub;
    $('waitText').textContent='ライバルが狙っている…（'+(m.sub==='select'?'打ち方をえらび中':TYPE_NAMES[m.type])+'）';showPanel('pWait')}}
  else if(m.t==='shot'){if(game.phase==='wait'&&!isMyTurn())fireShot(m);else game.pendingShot=m}
  else if(m.t==='pass'){if(game.phase==='wait'&&!isMyTurn())passTurn();else game.pendingShot={pass:1}}
  else if(m.t==='stallwin'){if(game.phase!=='over'&&game.phase!=='title'){toast('時間切れのまま反応がなかったため負けになりました');endMatch(1-myIdx())}}
  else if(m.t==='settle'){game.pendingSettle={st:m.st,at:game.realT}}
  else if(m.t==='again'){game.againRemote=true;checkAgain()}
}
function checkAgain(){
  if(game.mode!=='net'||game.ranked)return;
  if(game.againMe&&game.againRemote&&game.me===0){const seed=(Math.random()*1e9)|0;netSend({t:'start',seed,first:1,types:game.types});startMatch('net',seed,1,game.types)}
  else if(game.againRemote&&!game.againMe&&game.phase==='over')$('bAgain').textContent='もう一回！（相手は準備OK）';
}

// ================= ランクマッチ（Firebase） =================
// ↓ Firebaseコンソール「プロジェクトの設定 → マイアプリ（ウェブ）」の firebaseConfig をそのまま貼る
const FIREBASE_CONFIG={
  apiKey:"AIzaSyDDR-4nuugeyakM9Zf9WbR1oarwpIOjRYU",
  authDomain:"zirihinit-games.firebaseapp.com",
  projectId:"zirihinit-games",
  storageBucket:"zirihinit-games.firebasestorage.app",
  messagingSenderId:"1052102781874",
  appId:"1:1052102781874:web:8a0ccf72dbff509f99d2ab"
};
// ランクマッチが使える場所（Firebaseの承認済みドメインと合わせる）
const RK_HOSTS=['zirihinit.github.io','localhost','127.0.0.1'];
const RK_URL='https://zirihinit.github.io/gekiochi/';
// ===== 遊ばれた回数（日ごとの合計だけ。誰が遊んだかは記録しない） =====
const STAT_EV=new Set(["open", "open_new", "howto", "shot1", "gt_start", "gt_win1", "gt_win2", "gt_win3", "gt_win4", "gt_win5", "gt_lose1", "gt_lose2", "gt_lose3", "gt_lose4", "gt_lose5", "gt_lose6", "net_host", "net_join", "net_start", "rank_open", "rank_human", "rank_bot", "rank_end", "gacha", "share", "pick_0", "vsw_0", "vsl_0", "pick_1", "vsw_1", "vsl_1", "pick_2", "vsw_2", "vsl_2", "pick_4", "vsw_4", "vsl_4", "pick_5", "vsw_5", "vsl_5", "src_direct", "src_x", "src_tiktok", "src_yt", "src_line", "src_search", "src_plicy", "src_portal", "src_other", "ch_open", "ch_start", "ch_beat", "ch_share", "inv_make", "inv_open", "inv_join"]);
const statOnce=new Set();
function stat(k,once){
  if(!STAT_EV.has(k)||(once&&statOnce.has(k)))return;statOnce.add(k);
  if(!/^https?:$/.test(location.protocol)||['localhost','127.0.0.1',''].includes(location.hostname)){if(!window.__statTest)return}
  const day=new Date(Date.now()+9*3600e3).toISOString().slice(0,10),P='projects/'+FIREBASE_CONFIG.projectId+'/databases/(default)/documents';
  const body={writes:[{transform:{document:P+'/gekiochi_stats/'+day,fieldTransforms:[{fieldPath:k,increment:{integerValue:'1'}}]}}]};
  try{fetch('https://firestore.googleapis.com/v1/'+P+':commit?key='+FIREBASE_CONFIG.apiKey,{method:'POST',keepalive:true,headers:{'Content-Type':'application/json'},body:JSON.stringify(body)}).catch(()=>{})}catch(e){}
}
const FB_VER='10.14.1',RK_K=32,COL={p:'gekiochi_players',q:'gekiochi_queue',m:'gekiochi_matches'};
const TIERS=[
  {min:-1e9,name:'消しカス',col:'#9a9aa8'},{min:1350,name:'落書きノート',col:'#62c46a'},{min:1450,name:'ふでばこ',col:'#3fb6f2'},
  {min:1550,name:'学級委員',col:'#f5b800'},{min:1650,name:'生徒会長',col:'#ff8a1a'},{min:1750,name:'校長先生',col:'#ff4b3e'},{min:1900,name:'激落王',col:'#a64bff'}];
const tierOf=r=>{let t=TIERS[0];for(const x of TIERS)if(r>=x.min)t=x;return t};
const RK={db:null,uid:null,prof:null,name:'',q:null,qtk:0};
try{RK.name=SAVE.getItem('gekiochiName')||''}catch(e){}
// 名前がまだなければ仮の名前を付ける（あとで「名前を変える」から変更できる）
function rkAutoName(){if(RK.name)return;RK.name='けしごむ'+String(1000+((Math.random()*9000)|0));RK.autoName=true;try{SAVE.setItem('gekiochiName',RK.name)}catch(e){}}
const rkRating=()=>RK.prof&&typeof RK.prof.rating==='number'?RK.prof.rating:1500;
// 消しカス（初回だけ100＝1回ぶん持っている）と、当てた景品
const GACHA_COST=100,KASU_WIN=30,KASU_LOSE=10,KASU_DUP=20;
const rkKasu=()=>RK.prof&&Number.isInteger(RK.prof.kasu)?RK.prof.kasu:100,rkInv=()=>RK.prof&&Array.isArray(RK.prof.inv)?RK.prof.inv.filter(x=>PRIZES[x]):[];
const rkBase=()=>Object.assign({name:RK.name,rating:1500,wins:0,losses:0,games:0},RK.prof||{},{name:RK.name,updated:Date.now()});
function mySave(){try{SAVE.setItem('gekiochiSkin',MY.skin);SAVE.setItem('gekiochiTitle',MY.title)}catch(e){}}
async function rkSaveProf(patch){const d=Object.assign(rkBase(),patch);RK.prof=d;try{await pRef().set(d);return true}catch(e){console.warn(e);return false}}
const safeType=k=>[0,1,2,3,4,5].includes(k|0)?k|0:0;
function loadScript(src){return new Promise((res,rej)=>{const s=document.createElement('script');s.src=src;s.onload=res;s.onerror=()=>rej(new Error('load '+src));document.head.appendChild(s)})}
async function rkInit(){
  if(RK.db)return true;
  if(!FIREBASE_CONFIG.apiKey){toast('ランクマッチは準備中です（サーバー未設定）');return false}
  if(!RK_HOSTS.includes(location.hostname)){toast('ランクマッチは公開版で遊べます → '+RK_URL.replace('https://',''));return false}
  toast('サーバーに接続中…');
  try{
    if(!window.firebase||!firebase.firestore)for(const f of['app','auth','firestore'])await loadScript(`https://cdn.jsdelivr.net/npm/firebase@${FB_VER}/firebase-${f}-compat.js`);
    if(!firebase.apps.length)firebase.initializeApp(FIREBASE_CONFIG);
    const auth=firebase.auth();
    let u=await new Promise(res=>{const un=auth.onAuthStateChanged(x=>{un();res(x)})});
    if(!u)u=(await auth.signInAnonymously()).user;
    RK.uid=u.uid;RK.db=firebase.firestore();
    const d=await RK.db.collection(COL.p).doc(RK.uid).get();RK.prof=d.exists?d.data():null;
    if(RK.prof&&RK.prof.name&&!RK.name)RK.name=RK.prof.name;
    if(RK.prof){const inv=allInv();MY.skin=inv.includes(RK.prof.skin)?RK.prof.skin:'';MY.title=inv.includes(RK.prof.title)?RK.prof.title:'';mySave()}
    $('toast').classList.add('hidden');return true;
  }catch(e){console.error(e);RK.db=null;toast('サーバーにつながりませんでした');return false}
}
const pRef=()=>RK.db.collection(COL.p).doc(RK.uid);
function sanitizeName(v){return String(v||'').replace(/[\u0000-\u001f\u007f<>]/g,'').trim().slice(0,10)}
function rkRenderLobby(){
  if(RK.db)rkSeatLobby();
  const r=Math.round(rkRating()),t=tierOf(r),i=TIERS.indexOf(t),n=TIERS[i+1],p=RK.prof||{};
  $('rkTier').textContent=t.name;$('rkTier').style.background=t.col;$('rkName').textContent=RK.name+' ✎';$('rkNameHint').classList.toggle('hidden',!RK.autoName);$('rkRate').textContent=r;
  $('rkWL').textContent=`${p.wins|0}勝 ${p.losses|0}敗`;
  $('rkKasu').textContent=rkKasu();gachaBadge();
  $('rkNext').textContent=n?`次の称号「${n.name}」まで あと ${n.min-r} pt`:'最高ランク！ 君こそ激落王だ';
}
function eraserIcon(k,sk){const d=document.createElement('div'),S2=SKINS[sk];d.className='eras k'+k;d.dataset.l=ETYPES[k].label;d.style.setProperty('--b','#'+(S2?S2.body:ETYPES[k].body).toString(16).padStart(6,'0'));return d}
function vsCard(el,name,rating,k,sk,ti){
  el.innerHTML='';const t=tierOf(rating);
  const a=document.createElement('div');a.className='vtier';a.style.background=t.col;a.textContent=t.name;
  const b=document.createElement('div');b.className='vn';b.textContent=name;
  const tl=document.createElement('div');tl.className='vtl';tl.textContent=TITLES[ti]?TITLES[ti].name:'';
  const c=document.createElement('div');c.className='vr';c.textContent=Math.round(rating)+' pt';
  const d=document.createElement('div');d.className='vt';d.textContent=ETYPES[k].name;
  el.append(a,tl,b,c,eraserIcon(k,sk),d);
}
function rkShowVs(){const q=RK.q;if(!q)return;
  game.oppSkin=safeSkin(q.opp.sk);game.oppTitle=safeTitle(q.opp.ti);
  vsCard($('vsL'),RK.name,rkRating(),game.myType,MY.skin,MY.title);vsCard($('vsR'),q.opp.name,q.opp.rating,safeType(q.opp.type),game.oppSkin,game.oppTitle);
  $('vsSub').textContent='接続中…';showScreen('rankVs');SFX.round();bgmPlay(null);bgmHit('crash');}
function rkCleanupQueue(){
  const q=RK.q;RK.q=null;if(!q)return;
  clearInterval(q.timer);clearTimeout(q.connTO);try{q.unsub&&q.unsub()}catch(e){}
  if(q.ref)q.ref.delete().catch(()=>{});
}
function rkQueueFail(msg){rkCleanupQueue();netClose();toast(msg);rkRenderLobby();showScreen('rankLobby')}
async function rkStartQueue(){
  if(!RK.db){showScreen('title');return}
  rkCleanupQueue();netClose();game.me=0;game.ranked=null;
  // 試合後の再戦でもタイトル状態に戻してから並ぶ
  game.token++;game.phase='title';chargeStop();$('hud').classList.add('hidden');
  S=newState(12345);buildObs(S.obs);applyLooks([0,0]);clearParts();
  const q={tk:++RK.qtk,t0:Date.now(),state:'connecting'};RK.q=q;
  const ic=$('qEras');ic.className='eras k'+game.myType;ic.dataset.l=ETYPES[game.myType].label;ic.style.setProperty('--b','#'+ETYPES[game.myType].body.toString(16).padStart(6,'0'));
  $('qTime').textContent='0:00';$('qSub').textContent='同じくらいの強さの相手を探し中';showScreen('rankQueue');
  if(!window.Peer){rkQueueFail('通信ライブラリを読み込めませんでした');return}
  const pid=PEER_PFX+'r'+Math.random().toString(36).slice(2,12);
  let peer;
  try{peer=await new Promise((res,rej)=>{const pp=new Peer(pid);const to=setTimeout(()=>rej(new Error('timeout')),12000);
    pp.on('open',()=>{clearTimeout(to);res(pp)});pp.on('error',e=>{clearTimeout(to);rej(e)})})}
  catch(e){if(RK.q===q)rkQueueFail('通信サーバーにつながりませんでした');return}
  if(RK.q!==q){peer.destroy();return}
  net.peer=peer;
  peer.on('connection',c=>{if(net.conn||RK.q!==q){c.close();return}net.conn=c;c.on('open',()=>setupConn(c))});
  peer.on('error',e=>{if(RK.q===q&&q.state==='matched'&&e.type==='peer-unavailable')rkQueueFail('相手とつながりませんでした')});
  q.ref=RK.db.collection(COL.q).doc(RK.uid);q.ts=Date.now();
  try{await q.ref.set({uid:RK.uid,name:RK.name,rating:rkRating(),type:game.myType,sk:MY.skin,ti:MY.title,peerId:pid,status:'waiting',ts:q.ts,hb:q.ts,v:3})}
  catch(e){console.error(e);if(RK.q===q)rkQueueFail('マッチングに参加できませんでした');return}
  if(RK.q!==q){q.ref.delete().catch(()=>{});return}
  q.state='waiting';
  q.unsub=q.ref.onSnapshot(d=>{const x=d.data();if(RK.q!==q||!x)return;
    if(x.status==='matched'&&q.state==='waiting'&&x.by!==RK.uid&&x.opp){
      q.state='matched';q.role='host';q.matchId=x.matchId;q.opp=x.opp;rkShowVs();
      q.connTO=setTimeout(()=>{if(RK.q===q&&game.phase==='title')rkQueueFail('相手とつながりませんでした')},20000)}
  },e=>console.warn(e));
  q.timer=setInterval(()=>{if(RK.q!==q)return;const sec=((Date.now()-q.t0)/1000)|0;
    $('qTime').textContent=`${(sec/60)|0}:${String(sec%60).padStart(2,'0')}`;
    if(q.state==='waiting'){
      if(sec>12)$('qSub').textContent='相手のはばを広げて探し中…';
      if(sec>=(q.botSec||(q.botSec=RK_BOT_SEC-6+Math.random()*12))){rkFallbackBot(q);return}}
    if(q.state==='waiting'){if(sec%8===0)q.ref.update({hb:Date.now()}).catch(()=>{});if(sec%3===0)rkTryClaim(q)}},1000);
  rkTryClaim(q);
}
const RK_BOT_SEC=30;
// 待ち行列から安全に抜けてからCPU戦へ（抜ける直前に人とマッチしていたらそちらを優先）
async function rkFallbackBot(q){
  if(!q||RK.q!==q||q.state!=='waiting'||q.botting)return;q.botting=true;
  const ok=await RK.db.runTransaction(async t=>{const d=await t.get(q.ref);if(!d.exists||d.data().status!=='waiting')return false;t.delete(q.ref);return true})
    .catch(e=>{console.warn(e);return false});
  if(!ok||RK.q!==q||q.state!=='waiting'){q.botting=false;return}
  q.ref=null;rkCleanupQueue();netClose();rkStartBot();
}
const BOT_NAMES=['ねりけし職人','カドけし','ふでばこ番長','らくがき王','えんぴつ丸','じょうぎ先輩','しゅくだい忘れ','ねむねむ','きゅうしょく当番','けしカス集め',
  'そうた','はると','ゆい','みお','りく','あおい','ゆうま','ひなた','KESHI','gomu_ojisan','消しゴム研究部','2B派','HB派','シャー芯折れた'];
function rkStartBot(){
  const r=rkRating(),diff=r<1450?0:r<1650?1:2,bt=randType(),first=(Math.random()*2)|0;
  let name;do{name=BOT_NAMES[(Math.random()*BOT_NAMES.length)|0]}while(name===RK.name);
  const opp={uid:'cpu',name,rating:Math.round(r+(Math.random()*2-1)*45),bot:true};
  const pick=o=>{const k=Object.keys(o);return k[(Math.random()*k.length)|0]};
  game.oppSkin=Math.random()<0.4?pick(SKINS):'';game.oppTitle=Math.random()<0.5?pick(TITLES):'';
  vsCard($('vsL'),RK.name,r,game.myType,MY.skin,MY.title);vsCard($('vsR'),opp.name,opp.rating,bt,game.oppSkin,game.oppTitle);
  $('vsSub').textContent='接続中…';setTimeout(()=>{$('vsSub').textContent='バトル開始！'},700+Math.random()*700);
  showScreen('rankVs');SFX.round();bgmPlay(null);bgmHit('crash');
  const tk=++RK.qtk;
  setTimeout(()=>{if(RK.qtk!==tk||game.phase!=='title'||$('rankVs').classList.contains('hidden'))return;
    game.diff=diff;game.me=0;
    game.ranked={matchId:'cpu-'+Date.now(),opp,done:false,K:RK_K/2,bot:true};stat('rank_bot');
    game.ranked.startP=rkReportStart();
    startMatch('cpu',(Math.random()*1e9)|0,first,[game.myType,bt]);
  },2400);
}
async function rkTryClaim(q){
  if(RK.q!==q||q.state!=='waiting'||q.claiming)return;q.claiming=true;
  try{
    const snap=await RK.db.collection(COL.q).where('status','==','waiting').limit(30).get();
    const now=Date.now(),myR=rkRating(),list=[];
    snap.forEach(d=>list.push(d.data()));
    const cands=list.filter(x=>x&&x.uid!==RK.uid&&x.v===3&&x.ts<q.ts&&now-x.hb<25000&&
      Math.abs(x.rating-myR)<=150+10*Math.max(now-x.ts,now-q.ts)/1000).sort((a,b)=>a.ts-b.ts);
    for(const c of cands){
      if(RK.q!==q||q.state!=='waiting')return;
      const cRef=RK.db.collection(COL.q).doc(c.uid),mRef=RK.db.collection(COL.m).doc();
      const res=await RK.db.runTransaction(async t=>{
        const a=await t.get(q.ref),b=await t.get(cRef);
        if(!a.exists||!b.exists||a.data().status!=='waiting'||b.data().status!=='waiting')return null;
        const bd=b.data(),me={uid:RK.uid,name:RK.name,rating:myR,type:game.myType,sk:MY.skin,ti:MY.title},op={uid:bd.uid,name:bd.name,rating:bd.rating,type:bd.type,sk:bd.sk||'',ti:bd.ti||''};
        t.update(cRef,{status:'matched',matchId:mRef.id,by:RK.uid,opp:me});
        t.update(q.ref,{status:'matched',matchId:mRef.id,by:RK.uid,opp:op});
        t.set(mRef,{p:[bd.uid,RK.uid],names:[bd.name,RK.name],ratings:[bd.rating,myR],types:[bd.type,game.myType],ts:Date.now()});
        return{peerId:bd.peerId,op};
      }).catch(e=>{console.warn(e);return null});
      if(res){
        if(RK.q!==q)return;
        q.state='matched';q.role='guest';q.matchId=mRef.id;q.opp=res.op;game.me=1;rkShowVs();
        const c2=net.peer.connect(res.peerId,{reliable:true});net.conn=c2;
        c2.on('open',()=>{setupConn(c2);netSend({t:'hello',rk:1,k:game.myType,matchId:q.matchId})});
        q.connTO=setTimeout(()=>{if(RK.q===q&&game.phase==='title')rkQueueFail('相手とつながりませんでした')},15000);
        return;
      }
    }
  }catch(e){console.warn(e)}finally{q.claiming=false}
}
async function rkOnHello(m){
  const q=RK.q;if(!q||game.me!==0||game.phase!=='title'||q.role==='guest')return;
  if(q.matchId!==m.matchId){
    try{const d=await q.ref.get(),x=d.data();
      if(!x||x.status!=='matched'||x.matchId!==m.matchId||!x.opp){try{net.conn.close()}catch(e){}net.conn=null;return}
      if(q.state!=='matched'){q.state='matched';q.role='host';q.matchId=x.matchId;q.opp=x.opp;rkShowVs()}
    }catch(e){return}
  }
  if(RK.q!==q)return;
  const types=[game.myType,safeType(m.k)],seed=(Math.random()*1e9)|0;
  netSend({t:'start',rk:1,seed,first:0,types});rkBegin(q,seed,0,types);
}
function rkOnStart(m){const q=RK.q;if(!q||q.role!=='guest'||game.phase!=='title')return;rkBegin(q,m.seed,m.first,(m.types||[0,0]).map(safeType))}
function rkBegin(q,seed,first,types){
  clearTimeout(q.connTO);$('vsSub').textContent='バトル開始！';
  const opp={uid:q.opp.uid,name:sanitizeName(q.opp.name)||'???',rating:+q.opp.rating||1500};
  setTimeout(()=>{
    if(RK.q!==q)return;
    rkCleanupQueue();
    game.ranked={matchId:q.matchId,opp,done:false};stat('rank_human');
    game.ranked.startP=rkReportStart();
    startMatch('net',seed,first,types);
  },1800);
}
async function rkReportStart(){
  const R=rkRating(),E=1/(1+Math.pow(10,(game.ranked.opp.rating-R)/400)),p=RK.prof||{},K=game.ranked.K||RK_K;
  Object.assign(game.ranked,{pre:R,E,K});
  // 先に「負け」で記録しておき、勝ったら上書き（途中で抜けると負けのまま）
  await rkSaveProf({rating:Math.round((R-K*E)*10)/10,wins:p.wins|0,losses:(p.losses|0)+1,games:(p.games|0)+1,last:game.ranked.matchId});
}
async function rkReportEnd(won){
  const g=game.ranked;if(!g||g.done)return;g.done=true;
  try{await g.startP}catch(e){}
  const gain=won?KASU_WIN:KASU_LOSE,p=RK.prof||{},kasu=rkKasu()+gain;
  await rkSaveProf(won?{rating:Math.round((g.pre+g.K*(1-g.E))*10)/10,wins:(p.wins|0)+1,losses:Math.max(0,(p.losses|0)-1),kasu}:{kasu});
  const pre=Math.round(g.pre),now=Math.round(rkRating()),dl=now-pre,t0=tierOf(pre),t1=tierOf(now),el=$('resRate');
  el.innerHTML='';
  const a=document.createElement('div');a.textContent='レート';
  const b=document.createElement('div');b.className='big';b.innerHTML=`${pre} → ${now} <span class="${dl>=0?'up':'dn'}">(${dl>=0?'+':''}${dl})</span>`;
  const c=document.createElement('div');c.textContent='称号：'+t1.name;
  el.append(a,b,c);
  if(t1!==t0){const e=document.createElement('div');e.className='tch';e.textContent=TIERS.indexOf(t1)>TIERS.indexOf(t0)?`ランクアップ！「${t1.name}」`:`ランクダウン…「${t1.name}」`;el.append(e)}
  const k=document.createElement('div');k.className='ks';k.innerHTML=`消しカス <b>+${gain}</b>（合計 ${kasu}）`+(kasu>=GACHA_COST?'<br>ガチャが引ける！':'');el.append(k);
  el.classList.remove('hidden');
}
// ===== ガチャ =====
function gachaBadge(){$('bGacha').classList.toggle('ready',!!(RK.db&&rkKasu()>=GACHA_COST))}
function gachaRender(){gachaBadge();const k=rkKasu();$('gaKasu').textContent=k;$('bPull').disabled=k<GACHA_COST||!!gachaRender.busy}
function prizeIcon(id){const p=PRIZES[id],d=document.createElement('span');
  if(SKINS[id]){d.className='sw';d.style.background='#'+p.body.toString(16).padStart(6,'0');d.style.setProperty('--s',p.sleeve)}else d.textContent='「'+p.name+'」';return d}
async function gachaPull(){
  if(gachaRender.busy||rkKasu()<GACHA_COST)return;gachaRender.busy=true;gachaRender();
  const r=Math.random(),rar=r<0.05?5:r<0.08?3:r<0.17?2:r<0.47?1:0,pool=Object.keys(PRIZES).filter(k=>PRIZES[k].rar===rar),id=pool[(Math.random()*pool.length)|0];
  const inv=rkInv(),dup=inv.includes(id),kasu=rkKasu()-GACHA_COST+(dup?KASU_DUP:0);
  const ok=await rkSaveProf({kasu,inv:dup?inv:inv.concat(id)});
  if(ok)stat('gacha');
  if(!ok){gachaRender.busy=false;gachaRender();toast('保存できませんでした。もう一度ためしてね');const d=await pRef().get().catch(()=>null);if(d&&d.exists)RK.prof=d.data();gachaRender();return}
  const cap=$('gaCap'),card=$('gaCard');card.classList.add('hidden');cap.style.visibility='';cap.classList.remove('shake');void cap.offsetWidth;cap.classList.add('shake');SFX.round();
  setTimeout(()=>{const p=PRIZES[id];cap.style.visibility='hidden';card.className='gaCard r'+p.rar;
    $('gaRar').textContent=RAR[p.rar];$('gaKind').textContent=SKINS[id]?'消しゴムのスキン':'称号';$('gaName').textContent=p.name;
    $('gaIcon').innerHTML='';$('gaIcon').append(prizeIcon(id));$('gaNote').textContent=dup?`もう持っている → 消しカス +${KASU_DUP}`:'NEW！ きせかえで使えるよ';
    p.rar>=2?SFX.win():p.rar===1?SFX.max():SFX.click();if(p.rar>=2)bgmHit(p.rar===3?'boom':'crash');
    gachaRender.busy=false;gachaRender()},950);
}
function gachaOpen(){$('gaCard').classList.add('hidden');$('gaCap').style.visibility='';gachaRender.busy=false;gachaRender();showScreen('rankGacha')}
// ===== きせかえ =====
function dressRender(){const inv=allInv();
  for(const[box,all,key,cnt]of[['drSkins',SKINS,'skin','drSkinN'],['drTitles',TITLES,'title','drTitleN']]){
    const el=$(box);el.innerHTML='';const ids=Object.keys(all);$(cnt).textContent=`${ids.filter(i=>inv.includes(i)).length} / ${ids.length}`;
    const mk=(id,label,own)=>{const b=document.createElement('button');b.className='drItem'+(MY[key]===id?' on':'')+(own?'':' lock');
      if(id&&own&&SKINS[id])b.append(prizeIcon(id));const t=document.createElement('span');t.textContent=label;b.append(t);
      if(id){const e=document.createElement('em');e.className='r'+all[id].rar;e.textContent=RAR[all[id].rar];b.append(e)}
      if(own)b.onclick=()=>{SFX.click();MY[key]=id;mySave();dressRender();rkSaveProf({skin:MY.skin,title:MY.title});applyLooks(game.types)};el.append(b)};
    mk('','なし',true);ids.forEach(id=>{const own=inv.includes(id);mk(id,own?all[id].name:'？？？',own)})}}
const SEATS=10;
function seatMsg(el,n,me){
  const t=n===0?'1位が空いてる！ 1戦すれば1位！':me===1?'いまあなたが1位！ 守りぬけ！':me&&n<SEATS?`いま${me}位！ 1位まであと${me-1}人`:!me&&n<SEATS?`トップ10に空席あり！ 1戦すればランクイン`:me?`いま${me}位！`:'';
  el.textContent=t;el.classList.toggle('hidden',!t)}
// ロビーにも今の順位・空席を出す（上位10人だけ読む）
async function rkSeatLobby(){const el=$('rkSeat');el.classList.add('hidden');
  try{const s=await RK.db.collection(COL.p).orderBy('rating','desc').limit(SEATS).get();if($('rankLobby').classList.contains('hidden'))return;
    seatMsg(el,s.size,[...s.docs].findIndex(d=>d.id===RK.uid)+1)}catch(e){console.warn(e)}}
async function rkShowBoard(){
  showScreen('rankBoard');const el=$('boardList');el.textContent='読み込み中…';$('boardMsg').classList.add('hidden');
  try{
    const s=await RK.db.collection(COL.p).orderBy('rating','desc').limit(50).get();el.innerHTML='';let i=0;
    s.forEach(d=>{i++;const x=d.data()||{},r=+x.rating||0,t=tierOf(r),row=document.createElement('div');row.className='brow'+(d.id===RK.uid?' me':'');
      const no=document.createElement('span');no.className='bno';no.textContent=i;
      const ti=document.createElement('span');ti.className='btier';ti.style.background=t.col;ti.textContent=t.name;
      const nm=document.createElement('span');nm.className='bnm';nm.textContent=sanitizeName(x.name)||'???';if(TITLES[x.title]){const sm=document.createElement('small');sm.textContent=TITLES[x.title].name;nm.append(sm)}
      const rt=document.createElement('span');rt.className='brt';rt.textContent=Math.round(r);
      const wl=document.createElement('span');wl.className='bwl';wl.textContent=`${x.wins|0}勝${x.losses|0}敗`;
      row.append(no,ti,nm,rt,wl);el.appendChild(row)});
    // 10位までの空いている席を見せる（空いていることが挑戦する理由になる）
    for(let k=i+1;k<=SEATS;k++){const row=document.createElement('div');row.className='brow empty'+(k===i+1?' first':'');
      const no=document.createElement('span');no.className='bno';no.textContent=k;const nm=document.createElement('span');nm.className='bnm';
      nm.textContent=k===i+1?'空席　ここに入れる！':'空席';row.append(no,nm);el.appendChild(row)}
    const me=[...s.docs].findIndex(d=>d.id===RK.uid)+1;seatMsg($('boardMsg'),i,me);
  }catch(e){console.warn(e);el.textContent='読み込めませんでした'}
}
addEventListener('pagehide',()=>{if(RK.q&&RK.q.ref)try{RK.q.ref.delete()}catch(e){}});

// ================= 入力 =================
document.querySelectorAll('#typeRow button').forEach(b=>{b.addEventListener('pointerdown',e=>e.stopPropagation());b.onclick=()=>{ac();setShotMode(+b.dataset.m)}});
function volRender(){$('volBgm').value=Math.round(VOL.bgm*100);$('volSe').value=Math.round(VOL.se*100);
  $('volBgmN').textContent=Math.round(VOL.bgm*100);$('volSeN').textContent=Math.round(VOL.se*100);
  $('volBtn').textContent=VOL.bgm||VOL.se?'🔊':'🔇'}
function volSave(){try{SAVE.setItem('gekiochiVol',JSON.stringify(VOL))}catch(e){}}
volRender();
$('volBtn').onclick=e=>{e.stopPropagation();ac();$('volPanel').classList.toggle('hidden')};
for(const[id,k]of[['volBgm','bgm'],['volSe','se']]){const el=$(id);
  el.addEventListener('pointerdown',e=>e.stopPropagation());
  el.oninput=()=>{ac();VOL[k]=el.value/100;muted=VOL.se===0;if(SEOUT)SEOUT.gain.value=VOL.se;bgmVol();volRender()};
  el.onchange=()=>{volSave();if(k==='se')SFX.click()}}
$('volPanel').addEventListener('pointerdown',e=>e.stopPropagation());
document.addEventListener('pointerdown',e=>{if(!e.target.closest('#snd'))$('volPanel').classList.add('hidden')});
// どこかを最初に触ったら音を起動（スマホは操作するまで音を出せないため）
addEventListener('pointerdown',()=>ac(),{passive:true});addEventListener('keydown',()=>ac());
$('bRank').onclick=async()=>{ac();SFX.click();if(!await rkInit())return;stat('rank_open');
  rkAutoName();if(RK.prof&&RK.prof.name&&RK.prof.name!==RK.name)RK.name=RK.prof.name;rkRenderLobby();showScreen('rankLobby')};
$('bNameOk').onclick=async()=>{const n=sanitizeName($('nameIn').value);if(!n){toast('名前を入れてね');return}
  SFX.click();RK.name=n;RK.autoName=false;try{SAVE.setItem('gekiochiName',n)}catch(e){}
  if(RK.prof){RK.prof.name=n;pRef().update({name:n}).catch(e=>console.warn(e))}
  const af=rkReady.after;rkReady.after=null;
  if(af==='gacha')gachaOpen();else if(af==='title'){dressRender();showScreen('rankDress')}else{rkRenderLobby();showScreen('rankLobby')}};
$('nameIn').addEventListener('keydown',e=>{e.stopPropagation();if(e.key==='Enter')$('bNameOk').click()});
$('bNameBack').onclick=()=>{SFX.click();if(RK.name){rkRenderLobby();showScreen('rankLobby')}else showScreen('title')};
$('bRename').onclick=$('rkName').onclick=()=>{SFX.click();$('nameIn').value=RK.autoName?'':RK.name;showScreen('rankName')};
$('bQueue').onclick=()=>{SFX.click();game.pickFor='rank';showScreen('pickMenu')};
$('bBoard').onclick=()=>{SFX.click();rkShowBoard()};
let dressFrom='title';
// ガチャ・きせかえはタイトルから。サーバーと名前が要るので、なければ先に用意する
async function rkReady(){if(!await rkInit())return false;rkAutoName();return true}
$('bGacha').onclick=async()=>{ac();SFX.click();dressFrom='gacha';if(await rkReady())gachaOpen()};$('bPull').onclick=()=>{ac();gachaPull()};
$('bDress').onclick=async()=>{ac();SFX.click();dressFrom='title';if(await rkReady()){dressRender();showScreen('rankDress')}};
$('bGaDress').onclick=()=>{SFX.click();dressFrom='gacha';dressRender();showScreen('rankDress')};
$('bGaBack').onclick=()=>{SFX.click();dressFrom='title';showScreen('title')};
$('bDressBack').onclick=()=>{SFX.click();if(dressFrom==='gacha')gachaOpen();else showScreen('title')};
$('bBoardBack').onclick=()=>{SFX.click();rkRenderLobby();showScreen('rankLobby')};
$('bRankBack').onclick=()=>{SFX.click();showScreen('title')};
$('bQCancel').onclick=()=>{SFX.click();rkCleanupQueue();netClose();rkRenderLobby();showScreen('rankLobby')};
$('bCpu').onclick=()=>{ac();SFX.click();game.pickFor='cpu';showScreen('pickMenu')};
$('bNet').onclick=()=>{ac();SFX.click();game.pickFor='net';showScreen('pickMenu')};
const CARDC={0:'#ffd23f',1:'#5cc8ff',2:'#ff8fb8',3:'#ffe27a',4:'#d8cfb8',5:'#ffb066'};
const PICK_LIST=[0,1,2,4,5,3];
const canPick=k=>PLAYABLE.includes(k)||(k===3&&goldOpen());
try{const t=+SAVE.getItem('gekiochiType');if(canPick(t))game.myType=t}catch(e){}
const hexC=k=>'#'+ETYPES[k].body.toString(16).padStart(6,'0');
$('cards').innerHTML=PICK_LIST.map(k=>`<button class="card" role="radio" data-k="${k}" style="--c:${CARDC[k]};--b:${hexC(k)}"><div class="ic"><div class="eras k${k}" data-l=""></div></div><div class="tn">${ETYPES[k].short}</div></button>`).join('');
let pickSel=null;
function pickRender(){if(pickSel===null||!PICK_LIST.includes(pickSel))pickSel=canPick(game.myType)?game.myType:0;const k=pickSel,T=ETYPES[k],lock=!canPick(k);
  document.querySelectorAll('#cards .card').forEach(b=>{const kk=+b.dataset.k,on=kk===k;b.classList.toggle('on',on);b.classList.toggle('lock',!canPick(kk));b.querySelector('.tn').textContent=canPick(kk)?ETYPES[kk].short:'？？？';b.setAttribute('aria-checked',on)});
  const p=$('pickInfo');p.style.setProperty('--c',CARDC[k]);p.style.setProperty('--b',hexC(k));p.classList.toggle('lock',lock);
  p.innerHTML=`<div class="ic"><div class="eras k${k}" data-l="${T.label}"></div></div><div class="nm">${lock?'？？？':T.name}</div><div class="ds">${lock?'勝ち抜き戦で10人目の強敵を倒すと使えるようになる。':T.desc}</div>
  <div class="sts">${T.stats.map((v,j)=>`<div class="stat"><span>${STAT_NAMES[j]}</span><span class="bar">${[0,1,2,3,4].map(n=>`<i class="${!lock&&n<v?'on':''}"></i>`).join('')}</span></div>`).join('')}</div>`;
  $('bPickOk').disabled=lock;$('bPickOk').textContent=lock?'まだ使えない':'これで勝負！'}
pickRender();
document.querySelectorAll('#cards .card').forEach(b=>b.onclick=()=>{ac();pickSel=+b.dataset.k;if(canPick(pickSel))game.myType=pickSel;pickRender();
  if(!canPick(pickSel)){SFX.buzz();return}
  ({1:()=>SFX.flick(0.3),2:()=>SFX.boing(6),4:()=>SFX.flick(0.15),5:()=>SFX.boing(3)}[game.myType]||(()=>SFX.click()))()});
$('bPickOk').onclick=()=>{ac();SFX.click();try{SAVE.setItem('gekiochiType',game.myType)}catch(e){}
  if(game.pickFor==='rank')rkStartQueue();else if(game.pickFor==='cpu')gtGo(1);else{showScreen('netMenu');netStatus('部屋を作るか、相手から聞いた<br>4ケタのコードで入ってね')}};
$('bPickBack').onclick=()=>{SFX.click();if(game.pickFor==='rank'){rkRenderLobby();showScreen('rankLobby')}else showScreen('title')};
$('bHow').onclick=()=>{ac();SFX.click();openHowto(null)};
// ===== あそびかた（スライド） =====
let howSeen=false,howNext=null,hwIdx=0;
try{howSeen=SAVE.getItem('gekiochiHow')==='1'}catch(e){}
const HW_N=document.querySelectorAll('#hwTrack .hwSlide').length;
$('hwDots').innerHTML='<i></i>'.repeat(HW_N);
function hwGo(i){hwIdx=clamp(i,0,HW_N-1);$('hwTrack').style.transform=`translateX(${-100*hwIdx}%)`;
  document.querySelectorAll('#hwDots i').forEach((d,k)=>d.classList.toggle('on',k===hwIdx));
  $('hwPrev').disabled=hwIdx===0;$('hwNext').disabled=hwIdx===HW_N-1;
  if(howNext)$('bHowGo').textContent=hwIdx===HW_N-1?'わかった！あそぶ':'とばしてあそぶ';}
function openHowto(next){stat('howto');howNext=next||null;hwGo(0);
  $('bHowGo').classList.toggle('hidden',!howNext);$('bHowBack').classList.toggle('hidden',!!howNext);
  document.querySelector('.hwMore').open=false;showScreen('howto')}
function closeHowto(){howSeen=true;try{SAVE.setItem('gekiochiHow','1')}catch(e){}
  const n=howNext;howNext=null;if(n)n();else showScreen('title')}
$('hwPrev').onclick=()=>{SFX.click();hwGo(hwIdx-1)};$('hwNext').onclick=()=>{SFX.click();hwGo(hwIdx+1)};
$('bHowBack').onclick=()=>{SFX.click();closeHowto()};
$('bHowGo').onclick=()=>{SFX.click();closeHowto()};
{let sx=null,sy=0;const hw=$('hw');
  hw.addEventListener('pointerdown',e=>{if(e.target.closest('.hwNav'))return;sx=e.clientX;sy=e.clientY});
  hw.addEventListener('pointerup',e=>{if(sx===null)return;const dx=e.clientX-sx,dy=e.clientY-sy;sx=null;
    if(Math.abs(dx)>40&&Math.abs(dx)>Math.abs(dy)){SFX.click();hwGo(hwIdx+(dx<0?1:-1))}});
  hw.addEventListener('pointercancel',()=>sx=null);}
addEventListener('keydown',e=>{if($('howto').classList.contains('hidden'))return;
  if(e.key==='ArrowRight')hwGo(hwIdx+1);else if(e.key==='ArrowLeft')hwGo(hwIdx-1);else if(e.key==='Enter'&&howNext)closeHowto()});
// ===== ランクマッチの解禁設定 =====
// false：「近日解禁！」と表示して押せない ／ true：解禁
// '2026-11-18T21:00:00+09:00' のように日時を書くと、その日時に自動で解禁（それまでは日時を表示）
const RANKED_OPEN=true;
function rankedOpen(){if(RANKED_OPEN===true)return true;if(typeof RANKED_OPEN==='string')return Date.now()>=Date.parse(RANKED_OPEN);return false}
function rankedLabel(){if(typeof RANKED_OPEN==='string'){const d=new Date(RANKED_OPEN);return `${d.getMonth()+1}/${d.getDate()} ${d.getHours()}:${String(d.getMinutes()).padStart(2,'0')} 解禁！`}return '近日解禁！'}
// 初めて遊ぶときだけ、先にあそびかたを見せる
// はじめての人は説明を見せずに、ふつう消しゴムでそのまま1人目と勝負（指のお手本つき）
{const orig=$('bCpu').onclick;$('bCpu').onclick=function(...a){if(TUT.n===0&&!howSeen){ac();SFX.click();game.myType=0;game.pickFor='cpu';gtGo(1);return}return orig.apply(this,a)}}
if(!rankedOpen()){const b=$('bRank'),open=b.onclick;b.classList.add('locked');b.innerHTML='ランクマッチ<small>'+rankedLabel()+'</small>';
  b.onclick=function(...a){
    if(rankedOpen()){b.classList.remove('locked');b.textContent='ランクマッチ';b.onclick=open;return open.apply(this,a)}
    ac();SFX.click();toast('ランクマッチは'+rankedLabel()+' おたのしみに')}}

$('bNetBack').onclick=()=>{SFX.click();netClose();showScreen('pickMenu')};
gtBestText();
$('bHost').onclick=()=>{ac();netHost()};$('bJoin').onclick=()=>{ac();netJoin()};
$('codeIn').addEventListener('keydown',e=>{e.stopPropagation();if(e.key==='Enter')netJoin()});
$('bAgain').onclick=()=>{ac();SFX.click();
  if(game.ranked){game.ranked=null;netClose();rkStartQueue();return}
  if(game.mode==='cpu'){const g=game.gt;gtGo(g&&g.won?g.n+1:1)}
  else{game.againMe=true;netSend({t:'again'});$('bAgain').textContent='相手を待っています…';$('bAgain').disabled=true;checkAgain()}};
// スマホもPCも、文章入りのXの投稿画面を開く（共有シートだとXアプリがURLしか拾わないことがあるため）
{let nw=false;try{nw=!SAVE.getItem('gekiochiSeen');SAVE.setItem('gekiochiSeen','1')}catch(e){}stat('open');if(nw)stat('open_new')}
entryFromURL();
$('bRetry').onclick=()=>{ac();SFX.click();const g=game.gt;if(g)gtGo(g.n,false,true)};
$('bShare').addEventListener('click',()=>{SFX.click();stat('share')});
$('bToTitle').onclick=()=>{SFX.click();toTitle()};
addEventListener('keydown',e=>{
  if(e.repeat&&(e.key===' '||e.key==='Enter')){e.preventDefault();return}
  keys[e.key]=true;if(!isMyTurn()||!aiming())return;
  if('1234'.includes(e.key))setShotMode(+e.key-1);
  else if(e.key==='q'||e.key==='Q')setShotMode(3);else if(e.key==='e'||e.key==='E')setShotMode(2);
  else if(e.key==='t'||e.key==='T'||e.key==='Tab'){cycleShot();e.preventDefault()}
  else if((e.key===' '||e.key==='Enter')&&game.phase==='dir'&&!drag){toPower();e.preventDefault()}
});
addEventListener('keyup',e=>{keys[e.key]=false;
  if((e.key===' '||e.key==='Enter')&&game.kbCharge&&isMyTurn()){game.kbCharge=false;if(game.shot.power>=0.08)myFire();else{chargeStop();game.phase='dir';game.shot.power=0}}});
// 引っぱったときにページがスクロールしたり、アプリ内ブラウザが閉じたりしないようにする
for(const t of['touchstart','touchmove'])cv.addEventListener(t,e=>{if(e.cancelable)e.preventDefault()},{passive:false});
document.addEventListener('touchmove',e=>{if(e.cancelable&&!e.target.closest('.screen'))e.preventDefault()},{passive:false});
cv.addEventListener('pointerdown',e=>{ac();if(game.phase==='flying'&&game.flyT>0.6&&slowT<=0)game.ff=true;if(aimStart(e.clientX,e.clientY)){try{cv.setPointerCapture(e.pointerId)}catch(_){}}});
cv.addEventListener('pointermove',e=>aimMove(e.clientX,e.clientY));
cv.addEventListener('pointerup',()=>aimEnd());cv.addEventListener('pointercancel',()=>{drag=null;if(game.phase==='power'&&isMyTurn()){chargeStop();game.phase='dir';game.shot.power=0}});

// ================= 予測線 =================
// 本物の盤面（相手・文房具込み）で先読みして、相手に当たる所まで線を引く。
// 当たる場合は「相手がはじかれる向き」と「自分がはね返る向き」を矢印で見せる（長さ＝勢い）
function previewShot(sh,i,maxLen){
  const t=cloneState(S),ev=[];t.noLuck=true;launch(t,i,Object.assign({},sh));const e=t.e[i],o=t.e[1-i];
  const raw=[[e.x,Math.max(e.y,0),e.z]];let len=0,px=e.x,pz=e.z,hit=null,fall=false;
  for(let k=0;k<2400;k++){
    ev.length=0;step(t,DT,ev);len+=Math.hypot(e.x-px,e.z-pz);px=e.x;pz=e.z;
    if(ev.some(v=>v.k==='hit')){
      raw.push([e.x,Math.max(e.y,0),e.z]);const hx=e.x,hz=e.z;
      // 数ステップ進めて、ぶつかった直後の向きと速さを読む（線の先端は当たった瞬間の位置）
      for(let j=0;j<3;j++)step(t,DT,null);
      hit={ox:o.x,oz:o.z,ovx:o.vx,ovz:o.vz,ex:hx,ez:hz,evx:e.vx,evz:e.vz};break}
    if(k%2===1)raw.push([e.x,Math.max(e.y,0),e.z]);
    if(e.falling){fall=true;break}
    if(len>maxLen||isStill(e)){raw.push([e.x,Math.max(e.y,0),e.z]);break}
  }
  // 細かいガタつきをならす（横方向だけ移動平均、両端はそのまま）
  const W=6,sm=raw.map((p,k)=>{if(k<W||k>=raw.length-W)return p;let x=0,z=0;for(let j=-W;j<=W;j++){x+=raw[k+j][0];z+=raw[k+j][2]}return[x/(2*W+1),p[1],z/(2*W+1)]});
  // 道のりに沿って DOT_GAP ごとに点を置く（始点から数えるので、威力を変えても手前の点は動かない）
  const pts=[];let acc=DOT_GAP*0.8;
  for(let k=1;k<sm.length&&pts.length<dots.length;k++){const a=sm[k-1],b=sm[k],d=Math.hypot(b[0]-a[0],b[2]-a[2]);let u=0;
    while(acc<=d-u&&pts.length<dots.length){u+=acc;const f=u/d;pts.push([a[0]+(b[0]-a[0])*f,a[1]+(b[1]-a[1])*f+0.12,a[2]+(b[2]-a[2])*f]);acc=DOT_GAP}
    acc-=d-u}
  const end=sm[sm.length-1];
  return{pts,end:[end[0],end[1],end[2]],hit,fall};
}
let pvKey='',pvRes=null;
function previewCached(sh,i,maxLen){
  const k=[i,sh.type,sh.curve,sh.angle.toFixed(3),(+sh.power).toFixed(2),maxLen,S.e[0].x.toFixed(3),S.e[0].z.toFixed(3),S.e[1].x.toFixed(3),S.e[1].z.toFixed(3)].join();
  if(k!==pvKey||!pvRes){pvKey=k;pvRes=previewShot(Object.assign({},sh,{angle:+(+sh.angle).toFixed(3),power:+(+sh.power).toFixed(2)}),i,maxLen)}
  return pvRes}
const arrowMk=c=>{const g=new THREE.Group(),m=new THREE.MeshBasicMaterial({color:c,transparent:true,opacity:0.9,depthTest:false});
  const sh=new THREE.Mesh(new THREE.CylinderGeometry(0.07,0.07,1,10),m);sh.position.y=0.5;g.add(sh);
  const hd=new THREE.Mesh(new THREE.ConeGeometry(0.2,0.42,12),m);g.add(hd);g.userData={sh,hd};g.visible=false;g.renderOrder=5;scene.add(g);return g};
const pushArrow=arrowMk(0xff3b5c),backArrow={visible:false},fallMat=new THREE.MeshBasicMaterial({color:0xff3b5c});
const hitRing=new THREE.Mesh(new THREE.RingGeometry(0.42,0.56,32),new THREE.MeshBasicMaterial({color:0xff3b5c,transparent:true,opacity:0.9,side:THREE.DoubleSide,depthTest:false}));hitRing.rotation.x=-Math.PI/2;hitRing.visible=false;hitRing.renderOrder=5;scene.add(hitRing);
function setArrow(a,x,z,vx,vz,k){const sp=Math.hypot(vx,vz);if(sp<0.3){a.visible=false;return}
  const L=clamp(sp*k,0.35,3.2),dx=vx/sp,dz=vz/sp;a.visible=true;a.position.set(x,0.35,z);
  a.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0),new THREE.Vector3(dx,0,dz));
  a.userData.sh.scale.y=L;a.userData.sh.position.y=L/2;a.userData.hd.position.y=L+0.18}
const ht=document.getElementById('hitTag');
function updateAimViz(){
  let show=false,sh=game.shot,sub=game.phase;
  if(aiming()&&isMyTurn())show=true;
  else if(game.phase==='wait'&&(game.cpuAnim||game.remoteSub!=='select')){show=true;sub=game.remoteSub}
  if(!show){dots.forEach(d=>d.visible=false);arrowHead.visible=false;tipMark.visible=false;pushArrow.visible=hitRing.visible=false;ht.className='hidden';return}
  const pw=sub==='power',p=pw?Math.max(0.05,sh.power):0.55;
  const{pts,end,hit,fall}=previewCached(Object.assign({},sh,{power:p}),game.shooter,pw?1e9:5);
  const mat=dotMat[game.shooter];arrowHead.visible=false;
  dots.forEach((d,k)=>{if(k<pts.length){d.visible=true;d.material=fall&&k>=pts.length-3?fallMat:mat;d.position.set(...pts[k]);d.scale.setScalar(1)}else d.visible=false});
  // 先端：引っぱっている間だけ、止まる所／落ちる所に白フチの円（当たる時は相手の赤い輪で示す）
  tipMark.visible=pw&&!hit;if(tipMark.visible){tipMark.position.set(end[0],0.03,end[2]);tipMark.userData.ctr.material=fall?fallMat:mat}
  hitRing.visible=!!hit;
  if(hit){const o=S.e[1-game.shooter];hitRing.position.set(o.x,0.03,o.z);hitRing.scale.setScalar((o.sz||1)*(1+0.08*Math.sin(game.realT*9)))}
  // 矢印は引っぱっている間だけ（威力で長さが変わる）
  if(hit&&pw)setArrow(pushArrow,hit.ox,hit.oz,hit.ovx,hit.ovz,0.16);else pushArrow.visible=false;
  // 相手の頭上に「命中！ 強／中／弱」、自分が落ちる線なら「落ちる！」
  let tag='';if(pw&&hit){const os=Math.hypot(hit.ovx,hit.ovz),es=Math.hypot(hit.evx,hit.evz);
    tag='命中！ <b>'+(os>=11?'強':os>=6?'中':'弱')+'</b>'+(es>=6?'<small>自分も飛ぶ！</small>':'')}
  else if(pw&&fall)tag='落ちる！';
  if(tag){const o=fall&&!hit?pts[pts.length-1]:[S.e[1-game.shooter].x,0,S.e[1-game.shooter].z];
    tmpP.set(o[0],1.1,o[2]).project(camera);ht.innerHTML=tag;ht.className=fall&&!hit?'miss':'';
    ht.style.left=clamp((tmpP.x+1)/2*innerWidth,70,innerWidth-70)+'px';ht.style.top=clamp((1-tmpP.y)/2*innerHeight,150,innerHeight*0.6)+'px'}
  else ht.className='hidden';
}

// ================= カメラ =================
const tmpP=new THREE.Vector3(),tmpL=new THREE.Vector3();
function updateCamera(dt){
  let k=1-Math.exp(-dt*5),fov=60;
  const ph=game.phase;
  if(ph==='title'||ph==='over'){
    const t=game.realT*0.12;tmpP.set(Math.cos(t)*36,15,Math.sin(t)*25);tmpL.set(0,-1,0);k=1-Math.exp(-dt*2);
  }else if(aiming()||ph==='wait'){
    const e=S.e[game.shooter],a=game.shot.angle,dx=Math.cos(a),dz=Math.sin(a);
    const sub=ph==='wait'?game.remoteSub:ph;
    const pw=sub==='power'?game.shot.power:0,[dist,h,side,lk]=sub==='power'||sub==='dir'?[5.4+pw*1.1,2.8+pw*0.5,0.8,3.5]:[5.8,2.9,0,4.5];
    tmpP.set(e.x-dx*dist-dz*side,e.y+h,e.z-dz*dist+dx*side);tmpL.set(e.x+dx*lk,0,e.z+dz*lk);fov=60-pw*5;k=1-Math.exp(-dt*6);
    cam.dirA=a;
  }else{
    // 飛行中：一番速い消しゴムを追う
    const cur=S.e[camTarget],o=S.e[1-camTarget];
    const sp=e=>Math.hypot(e.vx,e.vz);
    if(!cur.falling&&!o.falling&&sp(o)>sp(cur)*1.3+0.5)camTarget=1-camTarget;
    const e=S.e[camTarget],s=sp(e);
    if(fallCam&&e.falling){
      tmpP.copy(fallCam.pos);tmpL.set(e.x,e.y+0.3,e.z);fov=58;k=1-Math.exp(-dt*4);
    }else{
      if(s>0.6)cam.dirA+=angDiff(cam.dirA,Math.atan2(e.vz,e.vx))*(1-Math.exp(-dt*4));
      const dx=Math.cos(cam.dirA),dz=Math.sin(cam.dirA);
      tmpP.set(e.x-dx*5,e.y+2.1+s*0.05,e.z-dz*5);tmpL.set(e.x+dx*3,e.y*0.7,e.z+dz*3);
      fov=60+Math.min(24,s*1.4);k=1-Math.exp(-dt*7);
    }
    speedFx+=(clamp((s-3)/9,0,1)*(slowT>0?0.4:1)-speedFx)*(1-Math.exp(-dt*8));
  }
  if(!(ph==='flying'))speedFx*=Math.exp(-dt*6);
  cam.pos.lerp(tmpP,k);cam.look.lerp(tmpL,k);cam.fov+=(fov-cam.fov)*(1-Math.exp(-dt*5));
  camera.position.copy(cam.pos);
  if(shake>0.001){camera.position.x+=(Math.random()-0.5)*shake*0.35;camera.position.y+=(Math.random()-0.5)*shake*0.35;camera.position.z+=(Math.random()-0.5)*shake*0.35;shake*=Math.exp(-dt*7)}
  camera.lookAt(cam.look);camera.fov=cam.fov;camera.updateProjectionMatrix();
}

// ================= 集中線 =================
// 集中線・ゴムひも・流線は画面に出さない2Dキャンバスに描いて、3Dの上に1枚の板として重ねる（canvasタグは1つだけ）
const fxc=document.createElement('canvas'),fxg=fxc.getContext('2d');let FXR=1,fxOn=false;
const fxTex=new THREE.CanvasTexture(fxc);fxTex.encoding=THREE.sRGBEncoding;fxTex.minFilter=fxTex.magFilter=THREE.LinearFilter;fxTex.generateMipmaps=false;
const fxScene=new THREE.Scene(),fxCam=new THREE.OrthographicCamera(-1,1,1,-1,0,1);
fxScene.add(new THREE.Mesh(new THREE.PlaneGeometry(2,2),new THREE.MeshBasicMaterial({map:fxTex,transparent:true,depthTest:false,depthWrite:false,toneMapped:false})));
let burst=null;
function startBurst(wx,wy,wz,p){const v=new THREE.Vector3(wx,wy,wz).project(camera);
  burst={t:0,dur:0.55+p*0.25,x:(v.x*0.5+0.5)*fxc.width,y:(-v.y*0.5+0.5)*fxc.height,p,seed:(Math.random()*1e6)|0}}
function drawFX(rdt){
  const pull=drag&&game.phase==='power'&&isMyTurn();
  if(!burst&&!pull&&speedFx<0.05){fxOn=false;return}
  fxOn=true;const w=fxc.width,h=fxc.height;fxg.clearRect(0,0,w,h);
  // 弾いた瞬間の集中線
  if(burst){
    burst.t+=rdt;const k=1-burst.t/burst.dur;
    if(k<=0)burst=null;else{
      const cx=burst.x,cy=burst.y,m=Math.hypot(Math.max(cx,w-cx),Math.max(cy,h-cy))*1.1;
      if(burst.t<0.07){fxg.fillStyle=`rgba(255,255,255,${0.75*(1-burst.t/0.07)})`;fxg.fillRect(0,0,w,h)}
      const r=mulberry32(burst.seed+((burst.t*30)|0)),n=110+(burst.p*80|0);
      const rIn=m*(0.1+0.05*burst.p+0.25*(1-k));
      for(let i=0;i<n;i++){
        const a=r()*Math.PI*2,wd=(0.004+r()*0.016)*(0.6+burst.p),ri=rIn*(0.8+r()*0.6);
        const dark=r()<0.72;
        fxg.fillStyle=dark?`rgba(18,10,35,${0.8*Math.min(1,k*1.6)})`:`rgba(255,255,255,${0.9*Math.min(1,k*1.6)})`;
        fxg.beginPath();fxg.moveTo(cx+Math.cos(a)*ri,cy+Math.sin(a)*ri);
        fxg.lineTo(cx+Math.cos(a-wd)*m,cy+Math.sin(a-wd)*m);fxg.lineTo(cx+Math.cos(a+wd)*m,cy+Math.sin(a+wd)*m);fxg.closePath();fxg.fill();
      }
      const g=fxg.createRadialGradient(cx,cy,0,cx,cy,rIn*1.2);
      g.addColorStop(0,`rgba(255,250,220,${0.85*k})`);g.addColorStop(1,'rgba(255,250,220,0)');fxg.fillStyle=g;fxg.fillRect(cx-rIn*1.2,cy-rIn*1.2,rIn*2.4,rIn*2.4);
    }
  }
  // 引っぱっている間のゴムひも（モンスト風）
  if(drag&&game.phase==='power'&&isMyTurn()){
    const pr=FXR,x0=drag.x0*pr,y0=drag.y0*pr,x1=drag.x*pr,y1=drag.y*pr,p=game.shot.power;
    const dx=x1-x0,dy=y1-y0,L=Math.hypot(dx,dy)||1,nx=-dy/L,ny=dx/L,hw=(16+p*30)*pr;
    fxg.lineJoin='round';fxg.beginPath();fxg.moveTo(x0,y0);fxg.lineTo(x1+nx*hw,y1+ny*hw);fxg.lineTo(x1-nx*hw,y1-ny*hw);fxg.closePath();
    fxg.fillStyle=p>0.9?'rgba(255,75,62,.92)':p>0.6?'rgba(255,210,63,.92)':'rgba(255,255,255,.9)';fxg.fill();
    fxg.strokeStyle='#1b1430';fxg.lineWidth=5*pr;fxg.stroke();
  }
  // 飛んでいる間の流線
  if(speedFx<0.05)return;
  const cx=w/2,cy=h*0.45,m=Math.hypot(cx,cy),n=10+(50*speedFx|0);
  for(let i=0;i<n;i++){const a=Math.random()*Math.PI*2,r1=m*(0.42+Math.random()*0.3),r2=r1+m*(0.25+Math.random()*0.6);
    fxg.strokeStyle=Math.random()<0.25?`rgba(255,220,90,${0.5*speedFx})`:`rgba(255,255,255,${0.55*speedFx})`;
    fxg.lineWidth=(1+Math.random()*5*speedFx)*FXR;fxg.beginPath();fxg.moveTo(cx+Math.cos(a)*r1,cy+Math.sin(a)*r1);fxg.lineTo(cx+Math.cos(a)*r2,cy+Math.sin(a)*r2);fxg.stroke()}
}

// ================= メインループ =================
function resize(){const w=innerWidth,h=innerHeight;renderer.setSize(w,h,false);camera.aspect=w/h;camera.updateProjectionMatrix();FXR=Math.min(1.5,window.devicePixelRatio||1);fxc.width=Math.round(w*FXR);fxc.height=Math.round(h*FXR);fxTex.dispose()}
addEventListener('resize',resize);resize();

function syncMeshes(dt){
  for(let i=0;i<2;i++){const e=S.e[i],m=eMesh[i],q=sq[i],mo=e.k===2;
    const K=mo?95:280,C=mo?4.5:17;q.vel+=(-K*q.v-C*q.vel)*dt;q.v=clamp(q.v+q.vel*dt,-0.4,0.45);
    const sp=Math.hypot(e.vx,e.vz),jig=m.jelly&&!e.falling?Math.min(0.09,sp*0.012)*Math.sin(game.realT*24+i):0;
    // プルン：ぶつかった後しばらく揺れが残る
    let pw=0,pr=0;if(m.pw>0.004&&!e.falling){m.pt=(m.pt||0)+dt;const ph=Math.sin(m.pt*26);pw=m.pw*ph;pr=m.pw*Math.cos(m.pt*26)*0.5;m.pw*=Math.exp(-dt*2.6)}else m.pw=0;
    const v=(e.falling?0:q.v)+jig,z=e.sz||1;m.g.scale.set((1+v*0.6+pw*0.55)*z,(1-v-pw*0.7)*z,(1+v*0.6-pw*0.25+pr*0.4)*z);if(m.anim===3&&m.skinTex)m.skinTex.offset.x=(game.realT*0.25)%1;else if(m.anim===1)m.body.material.color.setHSL((game.realT*0.3+i*0.5)%1,0.9,0.62);else if(m.anim===2)m.body.material.opacity=0.45+0.3*Math.sin(game.realT*3+i);
    m.g.position.set(e.x,e.y+EH/2*(1-v)*z,e.z);if(m.vib>0.003){m.g.position.x+=(Math.random()-0.5)*m.vib;m.g.position.z+=(Math.random()-0.5)*m.vib;m.vib*=hitstop>0?0.97:0.82}m.g.rotation.set(e.rx,-e.yaw,e.rz);
    const wb=game.phase==='title'?null:edgeWobble(e);
    if(wb){_wq.setFromAxisAngle(_wa.set(wb[1],0,-wb[0]),wb[2]*(0.55+0.45*Math.sin(game.realT*11+i*2)));m.g.quaternion.premultiply(_wq)}
    if(pr){_wq.setFromAxisAngle(_wa.set(0,0,1),pr*0.5);m.g.quaternion.multiply(_wq)}
    m.ring.visible=!e.falling&&game.phase!=='title';m.ring.position.set(e.x,0.015,e.z);
    const pulse=(game.phase!=='flying'&&i===game.shooter&&game.phase!=='title')?1+0.08*Math.sin(game.realT*6):1;m.ring.scale.setScalar(pulse);
  }
  syncObs();
}
let last=performance.now();
function frame(now){
  requestAnimationFrame(frame);
  const rdt=Math.min(0.05,(now-last)/1000);last=now;game.realT+=rdt;
  let ts=1;if(slowT>0){slowT-=rdt;ts=0.3}
  bgmUpdate();
  const ph=game.phase;
  if(ph==='flying'){
    // 決着に関係なさそうな「止まるまで」は早送り。タップでさらに速く
    if(ts===1&&game.flyT>0.5){const calm=S.e.every(e=>e.falling?e.y<=FLOOR:(Math.hypot(e.vx,e.vz)<3&&e.y<=0.01&&edgeDist(e)>2.5));
      if(game.ff)ts=6;else if(calm)ts=3}
    let sdt=rdt*ts;if(hitstop>0){hitstop-=rdt;sdt=0}
    acc+=sdt;let n=0;
    while(acc>=DT&&n<30){const ev=[];step(S,DT,ev);handleEvents(ev);acc-=DT;n++;game.flyT+=DT}
    if(settled(S)||game.flyT>14){if(game.flyT>14){S.e.forEach(e=>{if(!e.falling){e.vx=e.vy=e.vz=0;e.y=Math.max(0,e.y)}else e.y=FLOOR});S.obs.forEach(o=>{if(o.falling)o.y=FLOOR;else{o.vx=o.vz=o.w=0}})}onSettled()}
  }else if((ph==='dir'||ph==='power')&&isMyTurn()){
    const d=(keys.ArrowRight||keys.d||keys.D?1:0)-(keys.ArrowLeft||keys.a||keys.A?1:0);
    game.shot.angle+=d*1.4*rdt;
    if(ph==='power'&&game.kbCharge){const pp=game.shot.power;game.shot.power=Math.min(1,pp+rdt*0.8);chargeSet(game.shot.power);if(pp<0.96&&game.shot.power>=0.96)SFX.max()}
    if(ph==='power')shake=Math.max(shake,Math.max(0,game.shot.power-0.75)*0.2);
  }else if(ph==='wait'&&game.cpuAnim){
    const c=game.cpuAnim;c.t+=rdt;
    const k=c.k||1;
    if(c.t<1.3*k){game.remoteSub='dir';const u=c.t/(1.3*k),e=u<0.5?2*u*u:1-Math.pow(-2*u+2,2)/2;game.shot.angle=c.a0+angDiff(c.a0,c.sh.angle)*e}
    else if(c.t<2.3*k){if(game.remoteSub!=='power'){game.remoteSub='power';showPanel('pWait')}game.shot.angle=c.sh.angle;game.shot.power=c.sh.power*Math.min(1,(c.t-1.3*k)/(0.8*k))}
    else{game.cpuAnim=null;fireShot(c.sh)}
  }
  if(aiming()||ph==='wait')S.e[game.shooter].yaw=game.shot.angle;
  if(game.mode==='net'&&aiming()&&isMyTurn()){aimSendT-=rdt;if(aimSendT<=0){aimSendT=0.1;netSend({t:'aim',type:game.shot.type,angle:game.shot.angle,curve:game.shot.curve,power:game.shot.power,sub:ph})}}
  // ゲスト側：ホストの確定状態で同期
  if(game.mode==='net'&&game.me!==0&&game.pendingSettle){
    if(game.waitSettle||(ph==='flying'&&game.realT-game.pendingSettle.at>3)){
      applyState(S,game.pendingSettle.st);game.pendingSettle=null;game.waitSettle=false;game.phase='settling';later(resolveTurn,350);
    }
  }
  $('gauge').classList.toggle('hidden',!((ph==='power'&&isMyTurn())||(ph==='wait'&&game.remoteSub==='power')));
  tutUpdate();
  $('aimHint').style.opacity=!$('ghost').classList.contains('hidden')?0:(ph==='power'&&isMyTurn())?0.25:1;
  $('gfill').style.height=(game.shot.power*100).toFixed(1)+'%';$('gauge').classList.toggle('hot',game.shot.power>0.85);
  updateParts(rdt*ts);updateCamera(rdt);syncMeshes(rdt*ts);updateAimViz();updateFinger(rdt);drawFX(rdt);updateTimer();
  renderer.render(scene,camera);
  if(fxOn){fxTex.needsUpdate=true;renderer.autoClear=false;renderer.render(fxScene,fxCam);renderer.autoClear=true}
}
requestAnimationFrame(frame);

// ================= 挑戦状リンク・招待リンク =================
// ?c=人数.消しゴム.名前 … 勝ち抜き戦の挑戦状。開くと挑戦状画面 → 1タップで勝ち抜き戦へ
// ?room=1234 … ネット対戦の招待。開くと 1タップでその部屋に入る
// ?from=tt など … どこから来たかの集計用（名前は数えない、日ごとの合計だけ）
const BASE_URL='https://zirihinit.github.io/gekiochi/';
function chalName(){rkAutoName();return (RK.name||'').trim()||'けしごむ'}
function chalURL(wins,k){return BASE_URL+'?v=2&c='+wins+'.'+safeType(k)+'.'+encodeURIComponent(chalName().slice(0,10))}
function invURL(code){return BASE_URL+'?v=2&room='+code}
function chalCheck(n){const c=game.chal;if(!c||c.beat||n<=c.n)return;c.beat=true;stat('ch_beat');
  later(()=>toast(`${c.name}の記録（${c.n}人）を超えた！！`,2600,1),400)}
function invShow(code){const r=$('invRow');if(!r)return;r.classList.toggle('hidden',!code);invShow.code=code}
$('bInvLine').onclick=()=>{SFX.click();const c=invShow.code;if(!c)return;stat('inv_make');
  window.open('https://line.me/R/share?text='+encodeURIComponent('「激落！！消しゴムバトル！！」で勝負しよう！ タップでそのまま対戦👇\n'+invURL(c)),'_blank','noopener')};
$('bInvCopy').onclick=async()=>{SFX.click();const c=invShow.code;if(!c)return;stat('inv_make');
  const t='「激落！！消しゴムバトル！！」で勝負しよう！ タップでそのまま対戦👇\n'+invURL(c);
  try{await navigator.clipboard.writeText(t);toast('招待リンクをコピーしました')}catch(e){toast('コピーできませんでした。コード '+c+' を伝えてね')}};
$('bShareLine').addEventListener('click',()=>{SFX.click();stat('ch_share')});
$('bShare').addEventListener('click',()=>{if(!$('bShareLine').classList.contains('hidden'))stat('ch_share')});
function srcOf(qs){
  const f=(qs.get('from')||'').toLowerCase();
  const map={x:'x',tw:'x',twitter:'x',tt:'tiktok',tiktok:'tiktok',yt:'yt',youtube:'yt',line:'line',plicy:'plicy'};
  if(map[f])return map[f];
  if(location.hostname!=='zirihinit.github.io')return /plicy/i.test(location.hostname)?'plicy':'portal';
  let h='';try{h=document.referrer?new URL(document.referrer).hostname:''}catch(e){}
  if(!h||h===location.hostname)return 'direct';
  if(/(^|\.)(t\.co|x\.com|twitter\.com)$/.test(h))return 'x';
  if(/tiktok/.test(h))return 'tiktok';if(/youtube|youtu\.be/.test(h))return 'yt';if(/line\.me|line-apps/.test(h))return 'line';
  if(/plicy/.test(h))return 'plicy';if(/google\.|yahoo\.|bing\.|duckduckgo/.test(h))return 'search';
  return 'other'}
function entryFromURL(){
  let qs;try{qs=new URLSearchParams(location.search)}catch(e){return}
  const src=srcOf(qs);stat('src_'+src,true);
  const room=(qs.get('room')||'').trim(),c=qs.get('c');
  // もう一度読み込んだときに同じ画面が出ないように、URLから外しておく
  if(room||c||qs.get('from'))try{history.replaceState(null,'',location.pathname)}catch(e){}
  if(/^\d{4}$/.test(room)){stat('inv_open');
    $('chTag').textContent='対戦の招待';$('chFrom').textContent='友だちが部屋で待っています';
    $('chMain').textContent='部屋 '+room;$('chSub').textContent='消しゴムを指で弾いて、\n相手を机から落としたら勝ち！';
    $('bChGo').textContent='対戦する！';
    $('bChGo').onclick=()=>{ac();SFX.click();stat('inv_join');game.pickFor='net';showScreen('netMenu');$('codeIn').value=room;netJoin()};
    showScreen('challenge');return}
  const m=c&&/^(\d{1,3})\.([0-5])\.(.+)$/s.exec(c);
  if(m){const n=Math.min(999,+m[1]);if(n<1)return;
    const name=m[3].replace(/[\u0000-\u001f\u007f<>]/g,'').trim().slice(0,10)||'だれか';
    stat('ch_open');
    $('chTag').textContent='挑戦状';$('chFrom').textContent=name+' より';
    $('chMain').textContent=`勝ち抜き戦で\n${n}人激落！`;$('chSub').textContent=`${n+1}人倒せば、あなたの勝ち。\n消しゴムを指で弾いて、相手を机から落とせ！`;
    $('bChGo').textContent='受けて立つ！';
    $('bChGo').onclick=()=>{ac();SFX.click();stat('ch_start');game.chal={n,name,beat:false};game.pickFor='cpu';gtGo(1);
      later(()=>toast(`目標：${n+1}人激落で ${name} 超え！`,2600),300)};
    showScreen('challenge')}
}
$('bChSkip').onclick=()=>{SFX.click();showScreen('title')};
