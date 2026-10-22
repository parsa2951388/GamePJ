'use strict';
const http=require('http'),fs=require('fs'),cr=require('crypto'),path=require('path');
const PORT=process.env.PORT||3000,SPEED=+process.env.SPEED||1,SIZE=120;
const FILE=process.env.DATA_FILE||path.join(__dirname,'world.json');
const HTML=fs.readFileSync(path.join(__dirname,'index.html'));
// [wood,gold,iron,base seconds]
const BD={hall:[90,80,70,60],lumber:[50,60,40,40],gold:[65,50,40,45],iron:[75,65,70,50],farm:[80,60,50,45],store:[60,50,40,40],wall:[50,100,20,70],barracks:[200,170,90,90],stable:[270,240,260,120]};
const MX={wall:15,stable:15};
// c=cost t=sec a=attack d=defense s=min/field l=carry p=pop h=building r=min level
const U={
 pike:{c:[50,30,10],t:25,a:10,d:20,s:10,l:25,p:1,h:'barracks',r:1},
 guard:{c:[40,60,30],t:35,a:25,d:40,s:11,l:15,p:1,h:'barracks',r:3},
 raider:{c:[70,40,50],t:30,a:45,d:10,s:9,l:50,p:1,h:'barracks',r:5},
 knight:{c:[130,100,250],t:120,a:140,d:90,s:6,l:100,p:3,h:'stable',r:1}};
const RS=['w','g','i'],RB={w:'lumber',g:'gold',i:'iron'},has=Object.hasOwn;
let W={users:{},v:{},mv:[],chat:[],id:1},dirty=false;const TOK={};
const bad=m=>{throw{m}};
const K=v=>v.x+':'+v.y;
const P=l=>l?Math.round(45*1.2**(l-1))*SPEED:0,CAP=v=>Math.round(900*1.23**v.b.store),MAXPOP=v=>Math.round(90*1.2**v.b.farm);
const cost=(k,l)=>BD[k].slice(0,3).map(x=>Math.round(x*1.26**(l-1)));
const bt=(v,k,l)=>Math.max(1,Math.round(BD[k][3]*1.22**(l-1)*.96**v.b.hall/SPEED))*1e3;
const ut=(v,k)=>Math.max(1,Math.round(U[k].t*.94**v.b[U[k].h]/SPEED))*1e3;
const pend=(v,k)=>Math.max(v.b[k],...v.q.filter(q=>q.b===k).map(q=>q.lvl));
const int=x=>{x=Math.floor(+x);return x>0&&x<1e7?x:0};
const mk=(x,y,o,l)=>({x,y,o,n:o?'روستای '+o:'روستای شورشی',t:Date.now(),rt:Date.now(),r:{w:o?400:300,g:o?400:300,i:o?400:300},
 b:{hall:1,lumber:l,gold:l,iron:l,farm:1,store:l,wall:o?0:Math.max(0,l-3),barracks:o?1:0,stable:0},q:[],rq:[],tr:{pike:o?10:2*l},cap:3*l});
function seed(){let a=1337;const R=()=>{a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296};
 for(let n=0;n<1300;n++){const x=Math.floor(R()*SIZE),y=Math.floor(R()*SIZE),l=1+Math.floor(R()*7);if(!W.v[x+':'+y])W.v[x+':'+y]=mk(x,y,null,l)}}
try{W=JSON.parse(fs.readFileSync(FILE,'utf8'))}catch{seed()}
for(const k in W.users)TOK[W.users[k].tok]=k;

function adv(v,t){const d=(t-v.t)/36e5;
 if(d>0){const c=CAP(v);for(const r of RS)v.r[r]=Math.min(c,v.r[r]+P(v.b[RB[r]])*d)}
 v.t=Math.max(v.t,t);
 if(!v.o){const n=Math.floor((t-v.rt)/3e5);if(n>0){v.tr.pike=Math.min(v.cap,(v.tr.pike||0)+n);v.rt+=n*3e5}}}
function upd(v,now){
 while(v.q.length&&v.q[0].end<=now){const e=v.q.shift();adv(v,e.end);v.b[e.b]=e.lvl}
 while(v.rq.length&&v.rq[0].end<=now){const e=v.rq.shift();v.tr[e.u]=(v.tr[e.u]||0)+e.n}
 adv(v,now)}
const used=v=>{const k=K(v);let n=0;const add=o=>{for(const u in o)n+=o[u]*U[u].p};
 add(v.tr);v.rq.forEach(r=>n+=r.n*U[r.u].p);W.mv.forEach(m=>{if(m.h===k)add(m.tr)});return n};
const pay=(v,c)=>{if(RS.some((x,i)=>v.r[x]<c[i]))bad('منابع کافی نیست');RS.forEach((x,i)=>v.r[x]-=c[i])};
const diff=(a,b)=>{const o={};for(const k in a){const d=a[k]-(b[k]||0);if(d>0)o[k]=d}return o};

function battle(m){
 const t=W.v[m.to],h=W.v[m.h];upd(t,m.at);
 let A=0,D=0;for(const k in m.tr)A+=m.tr[k]*U[k].a;for(const k in t.tr)D+=t.tr[k]*U[k].d;
 D=(D+30)*(1+t.b.wall*.07);
 const win=A>D,had={...t.tr},sur={};
 if(win){const r=(D/A)**1.5;for(const k in m.tr)sur[k]=Math.floor(m.tr[k]*(1-r));t.tr={}}
 else{const r=(A/D)**1.5;for(const k in t.tr)t.tr[k]=Math.floor(t.tr[k]*(1-r))}
 const carry=Object.keys(sur).reduce((a,k)=>a+sur[k]*U[k].l,0),loot=[0,0,0];
 if(win&&carry>0){const tot=t.r.w+t.r.g+t.r.i,f=tot>0?Math.min(1,carry/tot):0;RS.forEach((x,j)=>{loot[j]=Math.floor(t.r[x]*f);t.r[x]-=loot[j]})}
 if(Object.values(sur).some(n=>n>0))W.mv.push({id:W.id++,k:'r',h:m.h,to:m.h,tr:sur,loot,at:m.at+(m.at-m.st)});
 const rep={id:W.id++,t:m.at,a:m.h,d:m.to,win,al:diff(m.tr,sur),dl:diff(had,t.tr),loot};
 [...new Set([h.o,t.o])].filter(Boolean).forEach(o=>{const r=W.users['@'+o].rep;r.unshift(rep);r.splice(30)})}
function back(m){const h=W.v[m.h];upd(h,m.at);for(const k in m.tr)h.tr[k]=(h.tr[k]||0)+m.tr[k];
 const c=CAP(h);RS.forEach((x,j)=>h.r[x]=Math.min(c,h.r[x]+m.loot[j]))}
function moves(now){for(;;){W.mv.sort((a,b)=>a.at-b.at);const m=W.mv[0];if(!m||m.at>now)break;W.mv.shift();m.k==='r'?back(m):battle(m)}}

const hash=(p,s)=>cr.scryptSync(p,s,32).toString('hex');
const auth=req=>{const n=TOK[(req.headers.authorization||'').slice(7)];if(!n)throw{m:'نشست نامعتبر',s:401};return W.users[n]};
function view(u,v,now){upd(v,now);return{n:u.n,now,x:v.x,y:v.y,
 r:{w:Math.floor(v.r.w),g:Math.floor(v.r.g),i:Math.floor(v.r.i)},prod:{w:P(v.b.lumber),g:P(v.b.gold),i:P(v.b.iron)},cap:CAP(v),pop:[used(v),MAXPOP(v)],b:v.b,q:v.q,rq:v.rq,
 bl:Object.keys(BD).map(k=>{const l=pend(v,k)+1;return{k,l:v.b[k],nl:l,c:cost(k,l),t:bt(v,k,l)/1e3,mx:l>(MX[k]||20)}}),
 ul:Object.keys(U).map(k=>({...U[k],k,t:ut(v,k)/1e3,n:v.tr[k]||0,ok:v.b[U[k].h]>=U[k].r})),
 mv:W.mv.filter(m=>W.v[m.h].o===u.n).map(m=>({k:m.k,to:m.to,at:m.at,loot:m.loot})),
 inc:W.mv.filter(m=>m.k==='a'&&W.v[m.to].o===u.n).map(m=>({from:m.h,at:m.at})),rep:u.rep}}

function api(p,b,q,req){
 const now=Date.now();moves(now);
 if(p==='register'){const n=String(b.name||''),pw=String(b.pw||'');
  if(!/^[\w\u0600-\u06FF]{3,16}$/.test(n))bad('نام کاربری: ۳ تا ۱۶ حرف یا عدد');
  if(pw.length<6)bad('رمز حداقل ۶ کاراکتر');if(W.users['@'+n])bad('این نام قبلاً گرفته شده');
  let x,y,k;do{x=20+Math.floor(Math.random()*(SIZE-40));y=20+Math.floor(Math.random()*(SIZE-40));k=x+':'+y}while(W.v[k]);
  const s=cr.randomBytes(8).toString('hex'),tok=cr.randomBytes(24).toString('hex');
  W.users['@'+n]={n,s,h:hash(pw,s),tok,vk:k,rep:[]};TOK[tok]='@'+n;W.v[k]=mk(x,y,n,1);return{tok}}
 if(p==='login'){const u=W.users['@'+b.name];if(!u||u.h!==hash(String(b.pw||''),u.s))bad('نام یا رمز اشتباه است');return{tok:u.tok}}
 const u=auth(req),v=W.v[u.vk];upd(v,now);
 switch(p){
 case 'state':return view(u,v,now);
 case 'build':{const k=b.b;if(!has(BD,k))bad('ساختمان نامعتبر');if(v.q.length>=5)bad('صف ساخت پر است');
  const l=pend(v,k)+1;if(l>(MX[k]||20))bad('به حداکثر سطح رسیده');pay(v,cost(k,l));
  const st=v.q.length?v.q[v.q.length-1].end:now;v.q.push({b:k,lvl:l,end:st+bt(v,k,l)});return view(u,v,now)}
 case 'recruit':{const k=b.u,n=int(b.n);if(!has(U,k)||!n)bad('تعداد نامعتبر');const d=U[k];
  if(v.b[d.h]<d.r)bad('ساختمان لازم به سطح کافی نرسیده');if(used(v)+n*d.p>MAXPOP(v))bad('ظرفیت مزرعه کافی نیست');
  pay(v,d.c.map(x=>x*n));const st=v.rq.length?v.rq[v.rq.length-1].end:now;v.rq.push({u:k,n,end:st+n*ut(v,k)});return view(u,v,now)}
 case 'attack':{const to=String(b.to||'').replace(/\s/g,''),t=W.v[to];if(!t)bad('روستایی در این مختصات نیست');
  if(t.o===u.n)bad('نمی‌توانید به خودتان حمله کنید');const tr={};let any=0;
  for(const k in b.tr||{}){if(!has(U,k))continue;const n=int(b.tr[k]);if(!n)continue;if(n>(v.tr[k]||0))bad('سرباز کافی در روستا نیست');tr[k]=n;any+=n}
  if(!any)bad('سربازی انتخاب نشده');for(const k in tr)v.tr[k]-=tr[k];
  const sp=Math.max(...Object.keys(tr).map(k=>U[k].s)),ms=Math.round(Math.hypot(t.x-v.x,t.y-v.y)*sp*6e4/SPEED);
  W.mv.push({id:W.id++,k:'a',h:K(v),to,tr,st:now,at:now+ms});return view(u,v,now)}
 case 'map':{const x=parseInt(q.get('x'))||0,y=parseInt(q.get('y'))||0,o=[];
  for(let j=y-8;j<=y+8;j++)for(let i=x-7;i<=x+7;i++){const t=W.v[i+':'+j];if(t)o.push({x:i,y:j,o:t.o,n:t.n,p:Object.values(t.b).reduce((a,c)=>a+c,0)})}
  return{v:o,size:SIZE}}
 case 'chat':{if(b.m!==undefined){const m=String(b.m).trim().slice(0,200);if(!m)bad('پیام خالی است');
  if(now-(u.lc||0)<1500)bad('کمی صبر کنید');u.lc=now;W.chat.push({u:u.n,m,t:now});if(W.chat.length>100)W.chat.shift()}
  return{c:W.chat.slice(-40)}}
 }
 bad('درخواست نامعتبر')}

const send=(res,c,o)=>{res.writeHead(c,{'content-type':'application/json; charset=utf-8','cache-control':'no-store'});res.end(JSON.stringify(o))};
const srv=http.createServer(async(req,res)=>{
 try{
  const u=new URL(req.url,'http://x');
  if(u.pathname==='/healthz')return res.end('ok');
  if(!u.pathname.startsWith('/api/')){res.writeHead(200,{'content-type':'text/html; charset=utf-8'});return res.end(HTML)}
  let b={};
  if(req.method==='POST'){req.setEncoding('utf8');let s='';for await(const c of req){s+=c;if(s.length>1e5)bad('حجم زیاد')}
   try{b=JSON.parse(s||'{}')}catch{bad('JSON نامعتبر')}if(!b||typeof b!=='object')b={};dirty=true}
  send(res,200,api(u.pathname.slice(5),b,u.searchParams,req));
 }catch(e){if(e&&e.m)send(res,e.s||400,{e:e.m});else{console.error(e);send(res,500,{e:'خطای سرور'})}}
});
const save=()=>{if(!dirty)return;dirty=false;fs.writeFile(FILE+'.tmp',JSON.stringify(W),e=>e?(dirty=true):fs.rename(FILE+'.tmp',FILE,()=>{}))};
setInterval(save,15e3);
setInterval(()=>{const n=Date.now();if(W.mv.some(m=>m.at<=n)){moves(n);dirty=true}},1e3);
for(const s of['SIGTERM','SIGINT'])process.on(s,()=>{try{fs.writeFileSync(FILE,JSON.stringify(W))}catch{}process.exit(0)});
srv.listen(PORT,()=>console.log('Server on http://localhost:'+PORT+' speed x'+SPEED));
