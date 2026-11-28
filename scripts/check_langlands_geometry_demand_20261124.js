// Langlands R184: source geometry discovery, bidirectional path residual and demanded residue evaluation.
function run(){
 const ck=(v,m)=>{if(!v)throw Error(m)};let seed=184;const rnd=n=>{seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return (seed>>>0)%n};
 const H=5,Z=[0,0,0],O=[1,0,0],red=(a,h)=>a.map(x=>((x%(2**h))+2**h)%(2**h)),add=(a,b,h)=>red(a.map((v,i)=>v+b[i]),h),sub=(a,b,h)=>red(a.map((v,i)=>v-b[i]),h),eq=(a,b)=>a.every((v,i)=>v===b[i]);
 function mul(a,b,h){let t=Array(5).fill(0);for(let i=0;i<3;i++)for(let j=0;j<3;j++)t[i+j]+=a[i]*b[j];for(let k=4;k>=3;k--){t[k-3]-=t[k];t[k-2]-=t[k]}return red(t.slice(0,3),h)}
 const val=a=>{let k=0;while(k<H&&a.every(x=>x%(2**(k+1))===0))k++;return k},bits=(n,x)=>Array.from({length:n},(_,i)=>(x>>i)&1),project=(x,S,T)=>T.reduce((a,v,i)=>a|(((x>>S.indexOf(v))&1)<<i),0),clause=(c,x)=>c.some(l=>x[Math.abs(l)-1]===+(l>0));
 function discover(n,F){
  const adj=Array.from({length:n},()=>new Set()),live=new Set(Array.from({length:n},(_,i)=>i)),bags=[],order=[],pos=[];let checks=0;
  for(const c of F){const s=[...new Set(c.map(l=>Math.abs(l)-1))];for(const i of s)for(const j of s)if(i!==j)adj[i].add(j)}
  while(live.size){let best=null;for(const i of live){const a=[...adj[i]].filter(j=>live.has(j));let fill=0;for(let p=0;p<a.length;p++)for(let q=p+1;q<a.length;q++){checks++;if(!adj[a[p]].has(a[q]))fill++}if(!best||fill<best.fill||(fill===best.fill&&a.length<best.a.length))best={i,a,fill}}
   const {i,a}=best;for(const j of a)for(const k of a)if(j!==k)adj[j].add(k);pos[i]=order.length;order.push(i);bags.push([i,...a].sort((a,b)=>a-b));live.delete(i)}
  bags.push([]);const edges=Array.from({length:n+1},()=>[]),parents=[];
  for(let t=0;t<n;t++){const s=bags[t].filter(i=>i!==order[t]),p=s.length?Math.min(...s.map(i=>pos[i])):n;parents[t]=p;edges[t].push(p);edges[p].push(t);ck(s.every(i=>bags[p].includes(i)),"separator")}
  const owners=F.map(c=>c.length?Math.min(...c.map(l=>pos[Math.abs(l)-1])):n);
  for(let j=0;j<F.length;j++)ck(F[j].every(l=>bags[owners[j]].includes(Math.abs(l)-1)),"factor scope");
  for(let i=0;i<n;i++){const B=new Set(bags.map((b,t)=>b.includes(i)?t:-1).filter(t=>t>=0)),seen=new Set(),q=[...B].slice(0,1);while(q.length){const t=q.pop();if(seen.has(t))continue;seen.add(t);for(const u of edges[t])if(B.has(u))q.push(u)}ck(seen.size===B.size,"running intersection")}
  return {bags,edges,parents,order,pos,owners,checks,peak:Math.max(...bags.map(b=>b.length))};
 }
 function local(n,F,w,d,pins,make){return d.bags.map((B,t)=>Array.from({length:2**B.length},(_,x)=>{let s=true,v=O;for(let j=0;j<F.length;j++)if(d.owners[j]===t&&!F[j].some(l=>((x>>B.indexOf(Math.abs(l)-1))&1)===+(l>0)))s=false;if(t<n){const i=d.order[t],b=(x>>B.indexOf(i))&1;v=w[i][b];if(pins.has(i)&&pins.get(i)!==b)s=false}return make(s?v:Z,s)}))}
 function model(n,F,w,d,pins=new Map()){
  const {bags,edges,pos}=d,L=local(n,F,w,d,pins,(v,s)=>({v,s})),cache=new Map();let built=0;
  const sep=(i,j)=>bags[i].filter(v=>bags[j].includes(v)),plus=(a,b)=>({v:add(a.v,b.v,H),s:a.s||b.s}),times=(a,b)=>({v:mul(a.v,b.v,H),s:a.s&&b.s}),zero={v:Z,s:false};
  function msg(i,j){const key=i+","+j;if(cache.has(key))return cache.get(key);built++;const S=sep(i,j),B=bags[i],C=edges[i].filter(k=>k!==j).map(k=>({S:sep(k,i),m:msg(k,i)})),a=Array(2**S.length).fill(zero),wit=Array(a.length).fill(-1);
   for(let x=0;x<L[i].length;x++){let v=L[i][x];for(const c of C)v=times(v,c.m.a[project(x,B,c.S)]);const k=project(x,B,S);a[k]=plus(a[k],v);if(v.s&&wit[k]<0)wit[k]=x}const m={a,wit};cache.set(key,m);return m}
  function root(i){const B=bags[i],C=edges[i].map(k=>({S:sep(k,i),m:msg(k,i)}));let a=zero,wx=-1;for(let x=0;x<L[i].length;x++){let v=L[i][x];for(const c of C)v=times(v,c.m.a[project(x,B,c.S)]);a=plus(a,v);if(v.s&&wx<0)wx=x}return {a,wx}}
  function witness(i){const r=root(i);if(!r.a.s)return null;const x=Array(n).fill(-1);function go(t,p,k){const B=bags[t];for(let j=0;j<B.length;j++){const v=(k>>j)&1;ck(x[B[j]]===-1||x[B[j]]===v,"witness compatibility");x[B[j]]=v}for(const u of edges[t])if(u!==p){const m=msg(u,t),s=project(k,B,sep(u,t));ck(m.wit[s]>=0,"witness exists");go(u,t,m.wit[s])}}go(i,-1,r.wx);return x}
  function path(i,j){const a=[];function rec(t,p){a.push(t);if(t===j)return true;for(const u of edges[t])if(u!==p&&rec(u,t))return true;a.pop();return false}ck(rec(i,-1),"path");return a}
  function transported(i,j,delta){const P=path(i,j);let prev=-1,arr=null,entries=0;for(let l=0;l<P.length;l++){const t=P[l],next=P[l+1]??-1,B=bags[t],S=prev<0?[]:sep(prev,t),T=next<0?[]:sep(t,next),C=edges[t].filter(k=>k!==prev&&k!==next).map(k=>({S:sep(k,t),m:msg(k,t)})),out=Array(2**T.length).fill(Z);
    for(let x=0;x<L[t].length;x++){entries++;let v=l===0?delta[x]:mul(L[t][x].v,arr[project(x,B,S)],H);for(const c of C)v=mul(v,c.m.a[project(x,B,c.S)].v,H);const k=project(x,B,T);out[k]=add(out[k],v,H)}arr=out;prev=t}return {v:arr[0],length:P.length,entries}}
  function pinDelta(v,b){const t=pos[v],B=bags[t];return L[t].map((x,k)=>((k>>B.indexOf(v))&1)===b?Z:sub(Z,x.v,H))}
  return {root,witness,transported,pinDelta,built:()=>built};
 }
 function precision(n,F,w,d,h,pins){
  const G=[],leaf=v=>{G.push({v,l:val(v),h:0});return G.length-1},gate=(op,a,b)=>{const l=op==="+"?Math.min(G[a].l,G[b].l):Math.min(H,G[a].l+G[b].l);G.push({op,a,b,l,h:0});return G.length-1},zero=leaf(Z),factors=local(n,F,w,d,pins,(v,s)=>s?leaf(v):zero),messages=[];
  for(let t=0;t<=n;t++){const B=d.bags[t],p=t<n?d.parents[t]:-1,S=p<0?[]:B.filter(i=>d.bags[p].includes(i)),out=Array(2**S.length).fill(zero);for(let x=0;x<factors[t].length;x++){let a=factors[t][x];for(const c of d.edges[t])if(c!==p){const m=messages[c];a=gate("*",a,m.a[project(x,B,m.S)])}const k=project(x,B,S);out[k]=gate("+",out[k],a)}messages[t]={S,a:out}}
  const root=messages[n].a[0];function demand(i,h){if(h>G[i].l)G[i].h=Math.max(G[i].h,h)}demand(root,h);
  for(let i=G.length-1;i>=0;i--){const g=G[i];if(!g.h||!g.op)continue;if(g.op==="+"){demand(g.a,g.h);demand(g.b,g.h)}else{demand(g.a,Math.max(0,g.h-G[g.b].l));demand(g.b,Math.max(0,g.h-G[g.a].l))}}
  let full=0,used=0,skipped=0,ops=0;for(const g of G){if(g.op)full+=h;if(!g.h){g.r=Z;if(g.op)skipped++;continue}if(!g.op){g.r=red(g.v,g.h);continue}const a=G[g.a].r,b=G[g.b].r;g.r=g.op==="+"?add(a,b,g.h):mul(a,b,g.h);used+=g.h;ops++}return {v:red(G[root].r,h),full,used,skipped,ops};
 }
 function brute(n,F,w,pins){let v=Z,s=false;for(let u=0;u<2**n;u++){const x=bits(n,u);if(!F.every(c=>clause(c,x))||[...pins].some(([i,b])=>x[i]!==b))continue;s=true;v=add(v,x.reduce((a,b,i)=>mul(a,w[i][b],H),O),H)}return {v,s}}
 let source=0,paths=0,witnesses=0,precisionChecks=0,probeChecks=0,full=0,used=0,skipped=0,neutral=0,mixed=0;const large=[];
 function fixture(n,F,w,small,unitControl=false){
  const d=discover(n,F),m=model(n,F,w,d),a=m.root(n).a,wx=m.witness(n);ck(!!wx===a.s&&(!wx||F.every(c=>clause(c,wx))),"original witness");if(wx)witnesses++;if(a.s&&eq(red(a.v,1),Z))neutral++;
  if(small){const b=brute(n,F,w,new Map());ck(eq(a.v,b.v)&&a.s===b.s,"source");source++}
  const i=rnd(n),j=(i+1+rnd(n-1))%n,bi=unitControl?1:rnd(2),bj=unitControl?1:rnd(2),p=new Map([[i,bi]]),q=new Map([[j,bj]]),pq=new Map([...p,...q]),mi=model(n,F,w,d,p),mj=model(n,F,w,d,q),mij=model(n,F,w,d,pq),ai=mi.root(n).a,aj=mj.root(n).a,aij=mij.root(n).a;
  const path=m.transported(d.pos[i],d.pos[j],m.pinDelta(i,bi)),path2=mi.transported(d.pos[j],d.pos[i],mi.pinDelta(j,bj)),path3=mj.transported(d.pos[i],d.pos[j],mj.pinDelta(i,bi));
  ck(eq(path.v,sub(ai.v,a.v,H))&&eq(path2.v,sub(aij.v,ai.v,H))&&eq(path3.v,sub(aij.v,aj.v,H)),"bidi path");paths+=3;ck(eq(sub(path2.v,sub(aj.v,a.v,H),H),sub(path3.v,path.v,H)),"mixed");mixed++;
  for(const [pinset,model0,a0] of [[p,mi,ai],[q,mj,aj],[pq,mij,aij]]){const x=model0.witness(d.pos[i]);ck(!!x===a0.s&&(!x||(F.every(c=>clause(c,x))&&[...pinset].every(([i,b])=>x[i]===b))),"pinned witness");if(x)witnesses++;if(small){const b=brute(n,F,w,pinset);ck(eq(a0.v,b.v)&&a0.s===b.s,"pinned source");source++}}
  if(unitControl)ck(!eq(red(aij.v,1),Z),'nonzero unit control');let localFull=0,localUsed=0;
  for(let h=1;h<=H;h++){const v=precision(n,F,w,d,h,pq);ck(eq(v.v,red(aij.v,h)),"actual low precision");precisionChecks++;if(h<=3){const base=precision(n,F,w,d,h,new Map());const A=w.reduce((a,x)=>mul(a,add(x[0],x[1],H),H),O);const D0=sub(mul([3,0,0],A,H),mul([4,0,0],a.v,H),H),D1=sub(mul([3,0,0],A,H),mul([4,0,0],aij.v,H),H);const delta=red(sub(D1,D0,H),h+2);ck(delta.every(x=>x%4===0)&&eq(delta.map(x=>x/4),sub(base.v,v.v,h)), 'Weil precision residual');probeChecks++}full+=v.full;used+=v.used;skipped+=v.skipped;localFull+=v.full;localUsed+=v.used}
  return {n,clauses:F.length,bag:d.peak,fillPairChecks:d.checks,path:path.length,pathEntries:path.entries,inhabited:aij.s,nonzeroMod2:!eq(red(aij.v,1),Z),full:localFull,used:localUsed};
 }
 for(let t=0;t<100;t++){const n=2+rnd(7),F=Array.from({length:rnd(12)},()=>Array.from({length:rnd(4)},()=> (rnd(2)?1:-1)*(1+rnd(n))));if(t%3===0)F.splice(0,F.length,...Array.from({length:n-1},(_,i)=>[i+1,-(i+2)]));const w=Array.from({length:n},()=>Array.from({length:2},()=>[rnd(32),rnd(32),rnd(32)].map(x=>x*(2**rnd(3))%32)));fixture(n,F,w,true)}
 for(const n of [31,63,127]){const F=[];for(let i=1;i<n;i+=2){const p=(i-1)>>1;F.push([p+1,i+1,i+2],[-(p+1),-(i+1),i+2],[p+1,-(i+1),-(i+2)])}const w=Array.from({length:n},()=>Array.from({length:2},()=>[rnd(32),rnd(32),rnd(32)].map(x=>x*(2**rnd(2))%32)));large.push(fixture(n,F,w,false));const wu=Array.from({length:n},()=>[[2,0,0],[1,1,0]]);large.push(fixture(n,F,wu,false,true))}
 return {source,paths,witnesses,precisionChecks,probeChecks,full,used,skipped,neutral,mixed,large};
}
console.log(JSON.stringify(run(),null,2));
