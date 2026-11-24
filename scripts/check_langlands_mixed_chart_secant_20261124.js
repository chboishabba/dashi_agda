// Langlands R191 onward: certified affine extraction, competing frontier charts, exact paired secants.
function run(){
 const ck=(b,m)=>{if(!b)throw Error(m)};let seed=191;const rnd=n=>{seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return(seed>>>0)%n};
 const Z=[0,0,0],O=[1,0,0],red=(a,h=5)=>a.map(v=>((v%(2**h))+2**h)%(2**h)),add=(a,b)=>red(a.map((v,i)=>v+b[i])),sub=(a,b)=>red(a.map((v,i)=>v-b[i])),scale=(a,k)=>red(a.map(v=>v*k)),eq=(a,b)=>a.every((v,i)=>v===b[i]);
 function mul(a,b){const t=Array(5).fill(0);for(let i=0;i<3;i++)for(let j=0;j<3;j++)t[i+j]+=a[i]*b[j];for(let k=4;k>=3;k--){t[k-3]-=t[k];t[k-2]-=t[k]}return red(t.slice(0,3))}
 const bit=i=>1n<<BigInt(i),par=x=>{let p=0;while(x){p^=1;x&=x-1n}return p},sat=(F,x)=>F.every(c=>c.some(l=>!!(x&bit(Math.abs(l)-1))===(l>0)));
 function parityClauses(S,s){const F=[];for(let a=0;a<2**S.length;a++)if(par(BigInt(a))!==s)F.push(S.map((i,k)=>((a>>k)&1)?-(i+1):i+1));return F}
 function extract(n,F){
  const groups=new Map(),taken=new Set(),rows=[];let scans=0;
  F.forEach((c,j)=>{scans++;if(c.length<2||c.length>3)return;const S=c.map(l=>Math.abs(l)-1).sort((a,b)=>a-b);if(new Set(S).size!==c.length)return;const key=S.join(","),a=c.reduce((v,l)=>v|(l<0?1<<S.indexOf(Math.abs(l)-1):0),0);if(!groups.has(key))groups.set(key,{S,m:new Map()});const g=groups.get(key);if(!g.m.has(a))g.m.set(a,[]);g.m.get(a).push(j)});
  for(const {S,m} of groups.values())for(const p of [0,1]){const A=Array.from({length:2**S.length},(_,a)=>a).filter(a=>par(BigInt(a))===p);if(A.every(a=>m.has(a))){rows.push({S,s:1-p});for(const a of A)for(const j of m.get(a))taken.add(j)}}
  const cols=Array(n).fill(0n);let target=0n;rows.forEach(({S,s},j)=>{for(const i of S)cols[i]|=bit(j);if(s)target|=bit(j)});
  return {rows,cols,target,F:F.filter((_,j)=>!taken.has(j)),scans,removed:taken.size};
 }
 function insert(B,x){for(let i=B.length-1;i>=0;i--)if(x&bit(i)){if(B[i])x^=B[i];else{B[i]=x;return}}}
 function member(B,x){for(let i=B.length-1;i>=0;i--)if(x&bit(i)){if(!B[i])return false;x^=B[i]}return x===0n}
 function build(n,F,kind,limit=60000){
  const E=kind==="mixed"?extract(n,F):{F,cols:Array(n).fill(0n),target:0n,rows:[],removed:0,scans:0},C=E.F;
  const end=Array(n).fill(0n),plus=Array(n).fill(0n),minus=Array(n).fill(0n),last=Array(n).fill(-1),ending=Array.from({length:n},()=>[]);let invalid=C.some(c=>!c.length);
  C.forEach((c,j)=>{if(!c.length)return;const m=Math.max(...c.map(l=>Math.abs(l)-1));end[m]|=bit(j);ending[m].push(c);for(const l of c){const i=Math.abs(l)-1;last[i]=Math.max(last[i],m);if(l>0)plus[i]|=bit(j);else minus[i]|=bit(j)}});
  const keep=Array.from({length:n},(_,k)=>last.reduce((a,v,i)=>v>k&&i<=k?a|bit(i):a,0n));
  const suffix=Array(n+1);suffix[n]=Array(E.rows.length).fill(0n);for(let k=n-1;k>=0;k--){suffix[k]=suffix[k+1].slice();insert(suffix[k],E.cols[k])}
  let cur=[[0n,0n]],layers=[],peak=1,attempts=0,states=1;
  if(invalid||!member(suffix[0],E.target))return {empty:true,peak:0,attempts:0,states:0,layers:[],E,rank:suffix[0].filter(Boolean).length};
  for(let k=0;k<n;k++){const next=[],idx=new Map(),edges=[];
   for(const [u,h] of cur){const e=[-1,-1];for(let b=0;b<2;b++){attempts++;if(attempts>limit)return {aborted:true,peak,attempts,states,E};let v=u,s=h^(b?E.cols[k]:0n);
    if(kind==="primal"){if(b)v|=bit(k);if(!sat(ending[k],v))continue;v&=keep[k]}else{v|=b?plus[k]:minus[k];if((v&end[k])!==end[k])continue;v&=~end[k]}
    if(!member(suffix[k+1],E.target^s))continue;
    const key=v.toString()+":"+s.toString();if(!idx.has(key)){idx.set(key,next.length);next.push([v,s])}e[b]=idx.get(key)}edges.push(e)}
   layers.push(edges);cur=next;states+=cur.length;peak=Math.max(peak,cur.length)
  }
  ck(cur.every(([v,s])=>v===0n&&s===E.target),"terminal state");
  return {layers,terminal:cur.length,peak,attempts,states,E,rank:suffix[0].filter(Boolean).length};
 }
 function quotient(G,n){
  if(G.empty)return {empty:true,layers:[],peak:0,states:0,attempts:0};
  let c=Array(G.terminal).fill(0),layers=Array(n),peak=G.terminal?1:0,states=peak;
  for(let k=n-1;k>=0;k--){const map=new Map(),next=[],ids=[];for(const e of G.layers[k]){const f=e.map(t=>t<0?-1:c[t]);if(f.every(t=>t<0)){ids.push(-1);continue}const key=f.join(",");if(!map.has(key)){map.set(key,next.length);next.push(f)}ids.push(map.get(key))}layers[k]=next;c=ids;peak=Math.max(peak,next.length);states+=next.length}
  if(c[0]<0)return {empty:true,layers:[],peak:0,states:0,attempts:G.attempts};
  ck(c[0]===0,"root quotient");return {layers,terminal:1,peak,states,attempts:2*(states-1)};
 }
 function evalG(G,n,w,pins=new Map()){
  if(G.empty)return {v:Z,s:false,witness:null,f:[],g:[]};
  const f=[[O]],bs=[[true]],g=Array(n+1),support=Array(n+1);
  for(let k=0;k<n;k++){const N=k===n-1?G.terminal:G.layers[k+1].length,a=Array(N).fill(Z),b0=Array(N).fill(false);for(let i=0;i<G.layers[k].length;i++)for(let b=0;b<2;b++){const j=G.layers[k][i][b];if(j<0||(pins.has(k)&&pins.get(k)!==b))continue;a[j]=add(a[j],mul(f[k][i],w[k][b]));b0[j]=b0[j]||bs[k][i]}f.push(a);bs.push(b0)}
  g[n]=Array(G.terminal).fill(O);support[n]=Array(G.terminal).fill(true);
  for(let k=n-1;k>=0;k--){g[k]=G.layers[k].map(e=>e.reduce((a,j,b)=>j<0||(pins.has(k)&&pins.get(k)!==b)?a:add(a,mul(w[k][b],g[k+1][j])),Z));support[k]=G.layers[k].map(e=>e.some((j,b)=>j>=0&&(!pins.has(k)||pins.get(k)===b)&&support[k+1][j]))}
  let x=null;if(support[0][0]){x=0n;let i=0;for(let k=0;k<n;k++){const b=G.layers[k][i].findIndex((j,b)=>j>=0&&(!pins.has(k)||pins.get(k)===b)&&support[k+1][j]);ck(b>=0,"witness");if(b)x|=bit(k);i=G.layers[k][i][b]}}
  const v=f[n].reduce(add,Z);ck(eq(v,g[0][0])&&bs[n].some(Boolean)===support[0][0],"forward reverse");
  return {v,s:!!support[0][0],witness:x,f,g};
 }
 function secant(G,n,w,p,q,old,neu){
  if(G.empty)return Z;let d=Z;
  for(let k=0;k<n;k++)for(let i=0;i<G.layers[k].length;i++)for(let b=0;b<2;b++){const j=G.layers[k][i][b];if(j<0)continue;const a=!p.has(k)||p.get(k)===b,c=!q.has(k)||q.get(k)===b;if(a===c)continue;d=add(d,mul(mul(old.f[k][i],scale(w[k][b],+c-+a)),neu.g[k+1][j]))}
  return d;
 }
 function brute(n,F,w,p){let v=Z,s=false;for(let x=0n;x<bit(n);x++){if(!sat(F,x)||[...p].some(([i,b])=>!!(x&bit(i))!==!!b))continue;s=true;let a=O;for(let i=0;i<n;i++)a=mul(a,w[i][+(!!(x&bit(i)))]);v=add(v,a)}return {v,s}}
 const same=(a,b)=>eq(a.v,b.v)&&a.s===b.s;
 let original=0,chart=0,quotients=0,extracts=0,secants=0,mixed=0,probes=0,witnesses=0,neutral=0,aborts=0,large=[];
 function fixture(n,F,w,small){
  const E=extract(n,F);if(small)for(let x=0n;x<bit(n);x++){let h=0n;for(let i=0;i<n;i++)if(x&bit(i))h^=E.cols[i];ck(sat(F,x)===(sat(E.F,x)&&h===E.target),"extraction BIDI");extracts++}
  const i=rnd(n),j=(i+1+rnd(n-1))%n,p=new Map([[i,rnd(2)]]),q=new Map([[j,rnd(2)]]),pq=new Map([...p,...q]),none=new Map(),P=[none,p,q,pq],G={},Q={},V={};
  for(const kind of ["primal","incidence","mixed"]){const g=build(n,F,kind,small?60000:30000);G[kind]=g;if(g.aborted){aborts++;continue}const h=quotient(g,n);Q[kind]=h;V[kind]=P.map(p=>evalG(g,n,w,p));
   P.forEach((pin,k)=>{const a=V[kind][k],b=evalG(h,n,w,pin);ck(same(a,b),"quotient");quotients++;if(a.s){ck(sat(F,a.witness)&&[...pin].every(([i,v])=>!!(a.witness&bit(i))===!!v),"original witness");ck(sat(F,b.witness)&&[...pin].every(([i,v])=>!!(b.witness&bit(i))===!!v),"quotient witness");witnesses+=2;if(eq(red(a.v,1),Z))neutral++}});
   const v=V[kind];for(const [a,b] of [[0,1],[0,2],[1,3],[2,3],[1,0],[2,0],[3,1],[3,2],[0,3],[3,0]]){ck(eq(secant(g,n,w,P[a],P[b],v[a],v[b]),sub(v[b].v,v[a].v)),"paired secant");secants++}
   const left=sub(sub(v[3].v,v[1].v),sub(v[2].v,v[0].v)),right=sub(sub(v[3].v,v[2].v),sub(v[1].v,v[0].v));ck(eq(left,right),"mixed");mixed++;
   const A=w.reduce((a,b)=>mul(a,add(...b)),O),D=v.map(x=>sub(scale(A,3),scale(x.v,4)));for(let h0=1;h0<=3;h0++){const d=red(sub(D[3],D[0]),h0+2);ck(d.every(x=>x%4===0)&&eq(d.map(x=>x/4),red(sub(v[0].v,v[3].v),h0)),"Weil");probes++}
  }
  for(const kind of Object.keys(V)){for(let k=0;k<4;k++){ck(same(V[kind][k],V.mixed[k]),"chart endpoint");chart++;if(small){ck(same(V[kind][k],brute(n,F,w,P[k])),"brute");original++}}}
  return {n,clauses:F.length,rows:E.rows.length,removed:E.removed,rank:G.mixed.rank,charts:Object.fromEntries(Object.keys(G).map(k=>[k,{peak:G[k].peak,attempts:G[k].attempts,states:G[k].states,aborted:!!G[k].aborted,quotientStates:Q[k]?.states,quotientPeak:Q[k]?.peak}])),base:V.mixed[0].v,inhabited:V.mixed[0].s};
 }
 for(let t=0;t<100;t++){const n=3+rnd(6),F=Array.from({length:rnd(10)},()=>Array.from({length:rnd(4)},()=> (rnd(2)?1:-1)*(1+rnd(n))));if(t%2===0)F.push(...parityClauses([0,1,2],rnd(2)));if(t%7===0)F.push(...parityClauses([0,1,2],0),...parityClauses([0,1,2],1));const w=Array.from({length:n},()=>Array.from({length:2},()=>[rnd(32),rnd(32),rnd(32)]));fixture(n,F,w,true)}
 for(const m of [6,12,24]){const n=6*m,F=[];for(let j=0;j<m;j++){const a=6*j,b=6*((j+1)%m);F.push([...Array.from({length:6},(_,k)=>a+k+1),...Array.from({length:6},(_,k)=>-(b+k+1))]);F.push(...parityClauses([a,a+1,a+2],1),...parityClauses([a+3,a+4,a+5],1),...parityClauses([a,b],0))}const w=Array.from({length:n},()=>[[2,0,0],[1,1,0]]);large.push(fixture(n,F,w,false))}
 return {original,chart,quotients,extracts,secants,mixed,probes,witnesses,neutral,aborts,large};
}
console.log(JSON.stringify(run(),null,2));
