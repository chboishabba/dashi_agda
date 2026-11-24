// Langlands integrated grouped crossing and chart-changing source strata.
function run(){
 const ck=(x,m)=>{if(!x)throw Error(m)};let seed=198;const rnd=n=>{seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)%n};
 const Z=[0,0,0],O=[1,0,0],H=5,red=(a,h=H)=>a.map(x=>((x%(2**h))+2**h)%(2**h)),add=(a,b,h=H)=>red(a.map((v,i)=>v+b[i]),h),sub=(a,b,h=H)=>red(a.map((v,i)=>v-b[i]),h),eq=(a,b)=>a.every((v,i)=>v===b[i]);
 function mul(a,b,h=H){let t=Array(5).fill(0);for(let i=0;i<3;i++)for(let j=0;j<3;j++)t[i+j]+=a[i]*b[j];for(let k=4;k>=3;k--){t[k-3]-=t[k];t[k-2]-=t[k]}return red(t.slice(0,3),h)}
 const bit=i=>1n<<BigInt(i),par=x=>{let p=0;while(x){p^=1;x&=x-1n}return p};
 const sat=(F,x)=>F.every(c=>c.some(l=>Boolean(x&bit(Math.abs(l)-1))===(l>0)));
 const pc=(S,s)=>Array.from({length:2**S.length},(_,a)=>a).filter(a=>par(BigInt(a))!==s).map(a=>S.map((i,j)=>a&(1<<j)?-i-1:i+1));
 function extract(n,F){
  const M=new Map(),used=new Set(),rows=[];
  F.forEach((c,j)=>{if(c.length<2||c.length>3)return;const S=c.map(l=>Math.abs(l)-1).sort((a,b)=>a-b);if(new Set(S).size!==c.length)return;const k=S.join(","),a=c.reduce((v,l)=>v|(l<0?1<<S.indexOf(Math.abs(l)-1):0),0);if(!M.has(k))M.set(k,{S,m:new Map()});const g=M.get(k).m;if(!g.has(a))g.set(a,[]);g.get(a).push(j)});
  for(const {S,m} of M.values())for(const p of [0,1]){const A=Array.from({length:2**S.length},(_,a)=>a).filter(a=>par(BigInt(a))===p);if(A.every(a=>m.has(a))){rows.push({S,s:1-p});for(const a of A)for(const j of m.get(a))used.add(j)}}
  const cols=Array(n).fill(0n),pos=Array(n).fill(0n),neg=Array(n).fill(0n);let target=0n;
  rows.forEach(({S,s},j)=>{for(const i of S)cols[i]|=bit(j);if(s)target|=bit(j)});
  const C=F.filter((_,j)=>!used.has(j));C.forEach((c,j)=>c.forEach(l=>{if(l>0)pos[l-1]|=bit(j);else neg[-l-1]|=bit(j)}));
  return {rows,cols,pos,neg,target,C,removed:used.size,invalid:C.some(c=>!c.length)};
 }
 let basisWork=0,obligationWork=0;
 function reduce(B,x){for(let i=B.length-1;i>=0;i--){basisWork++;if(B[i]&&(x&bit(i)))x^=B[i]}return x}
 function insert(B,x){x=reduce(B,x);if(x)B[x.toString(2).length-1]=x}
 function coordinates(B,x){let c=0n;for(let i=B.length-1;i>=0;i--)if(B[i]&&(x&bit(i))){x^=B[i];c|=bit(i)}ck(!x,"coordinate");return c}
 function decode(B,c){let x=0n;for(let i=0;i<B.length;i++)if(c&bit(i))x^=B[i];return x}
 function crossing(cols,target,r){
  const m=cols.length,B=Array(r).fill(0n),R=B.slice();for(let j=0;j<m;j++){let x=cols[j],y=bit(j);for(let i=r-1;i>=0;i--)if(B[i]&&(x&bit(i))){x^=B[i];y^=R[i]}if(x){let i=x.toString(2).length-1;B[i]=x;R[i]=y}}
  let x=target,sol=0n;for(let i=r-1;i>=0;i--)if(B[i]&&(x&bit(i))){x^=B[i];sol^=R[i]}if(x)return null;
  const suf=Array(m+1);suf[m]=Array(r).fill(0n);for(let k=m-1;k>=0;k--){suf[k]=suf[k+1].slice();insert(suf[k],cols[k])}
  let anchor=0n,peak=0;const cuts=[];
  for(let k=0;k<=m;k++){const Q=Array(r).fill(0n),V=Q.slice(),I=Q.slice();for(let j=0;j<k;j++){let u=reduce(suf[k],cols[j]),v=cols[j];for(let i=r-1;i>=0;i--)if(Q[i]&&(u&bit(i))){u^=Q[i];v^=V[i]}if(u){let i=u.toString(2).length-1;Q[i]=u;V[i]=v}else insert(I,v)}cuts.push({B:I,anchor});peak=Math.max(peak,I.filter(Boolean).length);if(k<m&&(sol&bit(k)))anchor^=cols[k]}
  return {cuts,suf,peak};
 }
 const nextSig=(s,b)=>((s&3)|(b?2:1))|(((s>>2)^b)<<2);
 function signatures(n){let S=new Set([0]);for(let i=0;i<n;i++)S=new Set([...S].flatMap(s=>[nextSig(s,0),nextSig(s,1)]));return [...S]}
 function compile(n,F,F2,single=false,canonical=true){
  const es=[extract(n,F),extract(n,F2)],groups=[],keys=new Map();
  for(let i=0;i<n;i++){const k=single?String(i):es.flatMap(e=>[e.pos[i],e.neg[i],e.cols[i]]).join(":");if(!keys.has(k)){keys.set(k,groups.length);groups.push([])}groups[keys.get(k)].push(i)}
  const m=groups.length,meta=es.map(e=>{const cols=groups.map(g=>e.cols[g[0]]),end=Array(m).fill(0n),last=Array(e.C.length).fill(-1);for(let k=0;k<m;k++){const a=e.pos[groups[k][0]]|e.neg[groups[k][0]];for(let j=0;j<last.length;j++)if(a&bit(j))last[j]=k}last.forEach((k,j)=>{if(k>=0)end[k]|=bit(j)});return {...e,cols,end,cross:e.invalid?null:crossing(cols,e.target,e.rows.length)}});
  function normalize(A){const S=[...new Set(A)].sort((a,b)=>a<b?-1:a>b?1:0);if(S.includes(0n))return null;const T=[];for(const x of S){let dominated=false;for(const y of S){obligationWork++;if(y!==x&&(x&y)===y){dominated=true;break}}if(!dominated)T.push(x)}return T}
  function obligations(e){const A=e.C.map(c=>c.reduce((a,l)=>a|bit(2*groups.findIndex(g=>g.includes(Math.abs(l)-1))+(l>0?1:0)),0n));return normalize(A.filter(x=>{for(let k=0;k<m;k++)if((x&(3n<<BigInt(2*k)))===(3n<<BigInt(2*k)))return false;return true}))}
  let cur=[meta.map(e=>{if(!e.cross)return null;const a=canonical?obligations(e):0n;return a===null?null:[a,0n]})],peak=1,total=1,attempts=0;const layers=[],sig=groups.map(g=>signatures(g.length));
  function step(e,u,k,s){if(!u)return null;const C=e.cross.cuts[k],N=e.cross.cuts[k+1],h=C.anchor^decode(C.B,u[1])^((s&4)?e.cols[k]:0n);if(reduce(e.cross.suf[k+1],e.target^h))return null;const i=groups[k][0];let a;
   if(canonical){const mask=3n<<BigInt(2*k),hit=BigInt(s&3)<<BigInt(2*k);a=normalize(u[0].filter(x=>!(x&hit)).map(x=>x&~mask));if(a===null)return null}
   else{a=u[0]|((s&1)?e.neg[i]:0n)|((s&2)?e.pos[i]:0n);if((a&e.end[k])!==e.end[k])return null;a&=~e.end[k]}
   return [a,coordinates(N.B,h^N.anchor)]}
  for(let k=0;k<m;k++){const next=[],idx=new Map(),edges=[];for(const u of cur){const row=[];for(const s of sig[k]){attempts++;ck(attempts<=200000,"cap");const v=u.map((x,i)=>step(meta[i],x,k,s));if(v.every(x=>!x)){row.push(-1);continue}const key=v.map(x=>x?String(x[0])+":"+String(x[1]):"dead").join("|");if(!idx.has(key)){idx.set(key,next.length);next.push(v)}row.push(idx.get(key))}edges.push(row)}layers.push(edges);cur=next;peak=Math.max(peak,cur.length);total+=cur.length}
  for(const u of cur)for(const s of u)if(s)ck((canonical?s[0].length===0:s[0]===0n)&&s[1]===0n,"terminal");
  return {groups,layers,sig,terminal:cur.map(u=>(u[0]?1:0)|(u[1]?2:0)),peak,total,attempts,cross:meta.map(e=>e.cross?.peak??0),rows:es.map(e=>e.rows.length),removed:es.map(e=>e.removed)};
 }
 function circuit(n,G,w,pins=new Map()){
  const N=[],users=[];function leaf(v,s){let i=N.length;N.push({v,s,op:"leaf"});users.push([]);return i}
  const z=leaf(Z,false),o=leaf(O,true);
  function gate(op,a,b){const i=N.length;N.push({op,a,b,v:Z,s:false});users.push([]);users[a].push(i);users[b].push(i);return i}
  const inp=w.map((v,i)=>v.map((x,b)=>leaf(pins.has(i)&&pins.get(i)!==b?Z:x,!pins.has(i)||pins.get(i)===b)));
  const packets=G.groups.map(g=>{let f=Array(8).fill(z);f[0]=o;for(const i of g){let t=Array(8).fill(z);for(let s=0;s<8;s++)for(let b=0;b<2;b++){const k=nextSig(s,b);t[k]=gate("+",t[k],gate("*",f[s],inp[i][b]))}f=t}return f});
  let f=[o];for(let k=0;k<G.groups.length;k++){const count=k+1===G.groups.length?G.terminal.length:G.layers[k+1].length,t=Array(count).fill(z);for(let i=0;i<G.layers[k].length;i++)for(let j=0;j<G.sig[k].length;j++){const a=G.layers[k][i][j];if(a>=0)t[a]=gate("+",t[a],gate("*",f[i],packets[k][G.sig[k][j]]))}f=t}
  const out=Array(4).fill(z);G.terminal.forEach((s,i)=>{out[s]=gate("+",out[s],f[i])});
  function calc(i){const g=N[i],a=N[g.a],b=N[g.b];return {v:g.op==="+"?add(a.v,b.v):mul(a.v,b.v),s:g.op==="+"?a.s||b.s:a.s&&b.s}}
  for(let i=0;i<N.length;i++)if(N[i].op!=="leaf")Object.assign(N[i],calc(i));
  let cachedLow=null;const values=()=>out.map(i=>({v:N[i].v,s:N[i].s}));
  function update(i,b,v,s){const id=inp[i][b];if(eq(N[id].v,v)&&N[id].s===s)return 0;cachedLow=null;Object.assign(N[id],{v,s});const dirty=new Set(users[id]);let count=0;for(let j=id+1;j<N.length;j++)if(dirty.has(j)){count++;const h=calc(j);if(!eq(h.v,N[j].v)||h.s!==N[j].s){Object.assign(N[j],h);for(const k of users[j])dirty.add(k)}}return count}
  function precision(h,probe){
   const val=a=>{let k=0;while(k<H&&a.every(x=>x%(2**(k+1))===0))k++;return k},L=[],low=[],d=Array(N.length).fill(0),R=[];let probeOps=0,full=0,used=0;
   for(let i=0;i<N.length;i++){const g=N[i];if(g.op==="leaf"){L[i]=val(g.v);if(probe)low[i]=cachedLow?cachedLow[i]:red(g.v,1)}else{L[i]=g.op==="+"?Math.min(L[g.a],L[g.b]):Math.min(H,L[g.a]+L[g.b]);full+=h;if(probe){low[i]=cachedLow?cachedLow[i]:(g.op==="+"?add(low[g.a],low[g.b],1):mul(low[g.a],low[g.b],1));if(eq(low[i],Z))L[i]=Math.max(L[i],1);if(!cachedLow)probeOps++}}}
   if(probe&&!cachedLow)cachedLow=low;const ask=(i,k)=>{if(k>L[i])d[i]=Math.max(d[i],k)};for(const i of out.slice(1))ask(i,h);
   for(let i=N.length-1;i>=0;i--){const g=N[i];if(!d[i]||g.op==="leaf")continue;ask(g.a,g.op==="+"?d[i]:Math.max(0,d[i]-L[g.b]));ask(g.b,g.op==="+"?d[i]:Math.max(0,d[i]-L[g.a]))}
   for(let i=0;i<N.length;i++){const g=N[i];if(!d[i])R[i]=Z;else if(g.op==="leaf")R[i]=red(g.v,d[i]);else{R[i]=g.op==="+"?add(R[g.a],R[g.b],d[i]):mul(R[g.a],R[g.b],d[i]);used+=d[i]}}
   return {v:out.map(i=>red(R[i],h)),full,used,probeOps};
  }
  return {values,update,precision,gates:N.filter(g=>g.op!=="leaf").length};
 }
 function brute(n,F,F2,w,pins){const a=Array.from({length:4},()=>({v:Z,s:false}));for(let x=0n;x<bit(n);x++){if([...pins].some(([i,b])=>Boolean(x&bit(i))!==Boolean(b)))continue;const k=+sat(F,x)+2*(+sat(F2,x));let v=O;for(let i=0;i<n;i++)v=mul(v,w[i][+Boolean(x&bit(i))]);a[k]={v:add(a[k].v,v),s:true}}return a}
 const same=(a,b)=>eq(a.v,b.v)&&a.s===b.s;
 function witness(G,pins,k){
  const packets=G.groups.map(g=>{let f=new Map([[0,0n]]);for(const i of g){const t=new Map();for(const [s,x] of f)for(const b of [0,1])if(!pins.has(i)||pins.get(i)===b){const a=nextSig(s,b);if(!t.has(a))t.set(a,x|(b?bit(i):0n))}f=t}return f});
  const g=Array(G.groups.length+1);g[G.groups.length]=G.terminal.map(s=>s===k);
  for(let i=G.groups.length-1;i>=0;i--)g[i]=G.layers[i].map(e=>e.some((j,t)=>j>=0&&packets[i].has(G.sig[i][t])&&g[i+1][j]));
  if(!g[0][0])return null;let x=0n,s=0;
  for(let i=0;i<G.groups.length;i++){const t=G.layers[i][s].findIndex((j,t)=>j>=0&&packets[i].has(G.sig[i][t])&&g[i+1][j]);ck(t>=0,"witness");x|=packets[i].get(G.sig[i][t]);s=G.layers[i][s][t]}return x;
 }
 let source=0,chart=0,prec=0,updates=0,witnesses=0,neutral=0,full=0,used=0,probeUsed=0,probeCost=0,updatedGates=0,fullGates=0,delta=0;const large=[];
 function fixture(n,F,F2,w,small){
  const before=basisWork,ow=obligationWork,G=compile(n,F,F2),cost=basisWork-before,oc=obligationWork-ow,J=compile(n,F,F2,true,false),raw=compile(n,F,F2,false,false),pins=new Map(),C=circuit(n,G,w),ref=circuit(n,J,w),rawC=circuit(n,raw,w);let localUpdate=0,localFull=0;
  function check(){
   const a=C.values(),b=ref.values();for(let k=1;k<=3;k++){ck(same(a[k],b[k])&&same(a[k],rawC.values()[k]),"chart");chart++;if(a[k].s){const x=witness(G,pins,k);ck(x!==null&&(+sat(F,x)+2*(+sat(F2,x)))===k&&[...pins].every(([i,b])=>Boolean(x&bit(i))===Boolean(b)),"source witness");witnesses++;if(eq(red(a[k].v,1),Z))neutral++}}
   if(small){const q=brute(n,F,F2,w,pins);for(let k=1;k<=3;k++){ck(same(a[k],q[k]),"brute");source++}}
   const old=add(a[1].v,a[3].v),neu=add(a[2].v,a[3].v),d=sub(neu,old);ck(eq(d,sub(a[2].v,a[1].v)),"gain loss");
   const A=w.reduce((v,z,i)=>mul(v,pins.has(i)?z[pins.get(i)]:add(...z)),O),D0=sub(mul([3,0,0],A),mul([4,0,0],old)),D1=sub(mul([3,0,0],A),mul([4,0,0],neu));
   for(let h=1;h<=3;h++){const r=red(sub(D1,D0),h+2);ck(r.every(x=>x%4===0)&&eq(r.map(x=>x/4),red(sub(Z,d),h)),"rank2");delta++}
   for(let h=1;h<=H;h++){const x=C.precision(h,false),y=C.precision(h,true);for(let k=1;k<=3;k++){ck(eq(x.v[k],red(a[k].v,h))&&eq(y.v[k],x.v[k]),"precision");prec++}full+=x.full;used+=x.used;probeUsed+=y.used;probeCost+=y.probeOps}
  }
  check();
  for(let t=0;t<3;t++){const i=rnd(n),b=rnd(2);if(pins.has(i)){pins.delete(i);localUpdate+=C.update(i,0,w[i][0],true)+C.update(i,1,w[i][1],true);localFull+=2*C.gates;ref.update(i,0,w[i][0],true);ref.update(i,1,w[i][1],true);rawC.update(i,0,w[i][0],true);rawC.update(i,1,w[i][1],true)}else{pins.set(i,b);localUpdate+=C.update(i,1-b,Z,false);localFull+=C.gates;ref.update(i,1-b,Z,false);rawC.update(i,1-b,Z,false)}
   const fresh=circuit(n,G,w,pins).values();for(let k=1;k<=3;k++)ck(same(C.values()[k],fresh[k]),"incremental");updates++;check()}
  updatedGates+=localUpdate;fullGates+=localFull;return {n,clauses:[F.length,F2.length],groups:G.groups.length,singleGroups:J.groups.length,rows:G.rows,removed:G.removed,cross:G.cross,peak:G.peak,singlePeak:J.peak,attempts:G.attempts,singleAttempts:J.attempts,basisCost:cost,obligationChecks:oc,rawGroupedPeak:raw.peak,rawGroupedAttempts:raw.attempts,gates:C.gates,singleGates:ref.gates,localUpdate,localFull};
 }
 for(let t=0;t<100;t++){const n=3+rnd(5),F=Array.from({length:rnd(8)},()=>Array.from({length:rnd(4)},()=> (rnd(2)?1:-1)*(1+rnd(n))));if(t%2===0)F.push(...pc([0,1,2],rnd(2)));const F2=F.slice();if(t%3===0&&F2.length)F2.splice(rnd(F2.length),1);else if(t%3===1)F2.push(...pc([0,1,2],rnd(2)));else F2.push([1]);const w=Array.from({length:n},()=>Array.from({length:2},()=>[rnd(32),rnd(32),rnd(32)]));fixture(n,F,F2,w,true)}
 for(const [m,k] of [[6,8],[12,16],[24,24]]){const n=m*k,F=[];for(let j=0;j<m;j++){const a=j*k,b=((j+1)%m)*k;F.push([...Array.from({length:k},(_,i)=>a+i+1),...Array.from({length:k},(_,i)=>-(b+i+1))]);F.push(...pc([a,a+1,a+2],1),...pc([a,b],0))}const F2=F.slice();F2.splice(1,1);F2.push([1]);const w=Array.from({length:n},()=>[[2,0,0],[1,1,0]]);large.push(fixture(n,F,F2,w,false))}
 const cancelF=[];for(let j=0;j<32;j++)cancelF.push(...pc([2*j,2*j+1],0));const cancellation=fixture(64,cancelF,[...cancelF,[1]],Array.from({length:64},()=>[O,O]),false);return {cancellation,source,chart,prec,updates,witnesses,neutral,full,used,probeUsed,probeCost,updatedGates,fullGates,delta,large};
}
console.log(JSON.stringify(run(),null,2));
