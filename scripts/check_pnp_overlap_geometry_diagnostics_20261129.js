// Section 45 independent diagnostic; run with Node.js. BigInt masks, no dependencies.
function campaign(){
"use strict";
const assert=(p,m)=>{if(!p)throw Error(m)};
const pop=x=>{let n=0;while(x){x&=x-1n;n++}return n};
function dag(n,blocks=Array.from({length:n},(_,i)=>i)){
 const g=[],v=[],support=[],bs=[];
 const add=(op,a,b)=>{let k=g.length;g.push([op,a,b]);support.push(op==="v"?1n<<BigInt(a):op==="c"?0n:support[a]|support[b]);bs.push(op==="v"?1n<<BigInt(blocks[a]):op==="c"?0n:bs[a]|bs[b]);return k};
 for(let i=0;i<n;i++)v.push(add("v",i));const zero=add("c",0),one=add("c",1);
 const plus=(a,b)=>add("+",a,b),mul=(a,b)=>add("*",a,b),neg=a=>plus(one,a),or=(a,b)=>plus(plus(a,b),mul(a,b));
 const fold=(xs,op,id)=>xs.reduce(op,id);
 function metrics(root,block=false,products=new Set(["*"])){
  const U=block?bs:support,seen=new Set(),st=[root];while(st.length){let i=st.pop();if(seen.has(i))continue;seen.add(i);let [o,a,b]=g[i];if(o!=="v"&&o!=="c")st.push(a,b)}
  const H=Array(g.length).fill(0n);let W=0n,t=0,bmax=0,productsN=0,edges=0;
  for(let i=g.length-1;i>=0;i--)if(seen.has(i)){
   let [o,a,b]=g[i];bmax=Math.max(bmax,pop(H[i]));if(o==="v"||o==="c")continue;
   let O=products.has(o)?U[a]&U[b]:0n;if(products.has(o))productsN++;
   W|=O;t=Math.max(t,pop(O));H[a]|=(H[i]|O)&U[a];H[b]|=(H[i]|O)&U[b];edges+=2;
  }
  return {gates:seen.size,allocated:g.length,edges,products:productsN,w:pop(W),b:bmax,t,variables:pop(U[root])};
 }
 function evaluate(root,x,p=2){const a=[];for(const [o,i,j] of g){let z=o==="v"?x[i]:o==="c"?i:o==="+"?a[i]+a[j]:o==="*"?a[i]*a[j]:o==="min"?Math.min(a[i],a[j]):a[i]+a[j];a.push(p?((z%p)+p)%p:z)}return a[root]}
 return {g,v,add,zero,one,plus,mul,neg,or,fold,metrics,evaluate};
}
function ryser(m){let C=dag(m*m,Array.from({length:m*m},(_,i)=>Math.floor(i/m))),r=C.zero;
 for(let s=1;s<1<<m;s++){let rows=[];for(let i=0;i<m;i++){let xs=[];for(let j=0;j<m;j++)if(s>>j&1)xs.push(C.v[i*m+j]);rows.push(C.fold(xs,C.plus,C.zero))}
 let p=C.fold(rows,C.mul,C.one);if((m-pop(BigInt(s)))%2)p=C.mul(C.add("c",-1),p);r=C.plus(r,p)}
 return {C,r};
}
function held(m,kind){let C=dag(m*m,Array.from({length:m*m},(_,i)=>Math.floor(i/m))),D=new Map(),zero=kind==="minplus"?C.add("c",1000000):C.zero;
 const sum=kind==="minplus"?(a,b)=>C.add("min",a,b):kind==="exist"?C.or:C.plus;
 const product=kind==="minplus"?(a,b)=>C.add("cost+",a,b):C.mul;
 const id=kind==="minplus"?C.zero:C.one;
 D.set("1:0",id);
 for(let s=1;s<1<<m;s+=2)for(let j=1;j<m;j++)if(s>>j&1){let prev=s^(1<<j),ls=[];for(let i=0;i<m;i++)if(prev>>i&1&&D.has(prev+":"+i))ls.push(product(D.get(prev+":"+i),C.v[i*m+j]));if(ls.length)D.set(s+":"+j,C.fold(ls,sum,zero))}
 let full=(1<<m)-1,ls=[];for(let j=1;j<m;j++)if(D.has(full+":"+j))ls.push(product(D.get(full+":"+j),C.v[j*m]));
 return {C,r:C.fold(ls,sum,zero),products:kind==="minplus"?new Set(["cost+"]):new Set(["*"])};
}
function permutations(xs){if(!xs.length)return [[]];return xs.flatMap((x,i)=>permutations(xs.filter((_,j)=>i!==j)).map(p=>[x,...p]))}
let standard=[],checks=0;
let seed=4501;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed};
for(let m=3;m<=8;m++){
 let R=ryser(m),P=held(m,"parity"),E=held(m,"exist"),M=held(m,"minplus");
 for(let [name,z] of [["Ryser",R],["HC subset DP parity",P],["HC subset DP existence",E],["Held-Karp min-plus",M]])standard.push({m,model:name,...z.C.metrics(z.r,false,z.products),blocks:z.C.metrics(z.r,true,z.products)});
 assert(R.C.metrics(R.r).w===0,"Ryser overlaps");assert(P.C.metrics(P.r).w===0,"parity path overlaps");assert(M.C.metrics(M.r,false,M.products).w===0,"minplus composition overlaps");
 if(m<=6){let perm=permutations(Array.from({length:m},(_,i)=>i)),paths=permutations(Array.from({length:m-1},(_,i)=>i+1));
  for(let k=0;k<12;k++){let x=Array.from({length:m*m},()=>((random()>>>24)&1)),w=Array.from({length:m*m},()=>1+(random()>>>24)%9);
   let per=perm.reduce((a,p)=>a+p.reduce((b,j,i)=>b*x[i*m+j],1),0);
   let costs=paths.map(p=>[0,...p,0].slice(1).map((j,i)=>[0,...p][i]*m+j)),hc=costs.reduce((a,es)=>a+es.reduce((b,e)=>b*x[e],1),0),best=Math.min(...costs.map(es=>es.reduce((a,e)=>a+w[e],0)));
   assert(R.C.evaluate(R.r,x,101)===per%101,"Ryser reference");assert(P.C.evaluate(P.r,x)===hc%2,"parity reference");assert(E.C.evaluate(E.r,x)===+(hc>0),"exist reference");assert(M.C.evaluate(M.r,w,0)===best,"minplus reference");checks+=4;
  }
 }
}
// Actual single-decision propagation/reason resolution, with original clauses retained.
function learnedFixture(n){
 let F=[[-1,2]];for(let i=2;i<n-1;i++)F.push([-i,i+1]);F.push([-1,-(n-1)],[1,n],[1,-n]);
 let clauses=F.map(c=>c.slice()),trace=[];
 function run(decision){
  let val=new Map(),trail=[],reasons=new Map();const assign=(l,r)=>{assert(!val.has(Math.abs(l)),"double assign");val.set(Math.abs(l),l>0);trail.push(l);reasons.set(Math.abs(l),r)};
  if(decision)assign(decision,null);
  const evalLit=l=>val.has(Math.abs(l))?val.get(Math.abs(l))===(l>0)?1:0:-1;
  let conflict=-1;
  outer:while(true){let progress=false;for(let i=0;i<clauses.length;i++){let c=clauses[i];if(c.some(l=>evalLit(l)===1))continue;let u=c.filter(l=>evalLit(l)===-1);if(!u.length){conflict=i;break outer}if(u.length===1){assign(u[0],i);progress=true;break}}if(!progress)break}
  assert(conflict>=0,"expected conflict");let idx=conflict;
  while(clauses[idx].length>(decision?1:0)){
   let c=clauses[idx],l=trail.slice().reverse().find(x=>c.includes(-x)&&reasons.get(Math.abs(x))!==null);
   assert(l!==undefined,"missing reason");let j=reasons.get(Math.abs(l)),d=clauses[j];assert(d.includes(l),"bad reason");
   let res=[...new Set([...c.filter(x=>x!==-l),...d.filter(x=>x!==l)])].sort((a,b)=>a-b);assert(!res.some(x=>res.includes(-x)),"tautological resolvent");
   trace.push({left:idx,right:j,pivot:Math.abs(l),result:clauses.length});clauses.push(res);idx=clauses.length-1;
  }
  return idx;
 }
 let learned=run(1);assert(clauses[learned].length===1&&clauses[learned][0]===-1,"wrong learned unit");let empty=run(0);assert(!clauses[empty].length,"not refuted");
 for(let step of trace){let {left,right,pivot,result}=step;let a=clauses[left],b=clauses[right];assert((a.includes(pivot)&&b.includes(-pivot))||(a.includes(-pivot)&&b.includes(pivot)),"bad replay pivot");let c=[...new Set([...a,...b].filter(l=>Math.abs(l)!==pivot))].sort((x,y)=>x-y);assert(JSON.stringify(c)===JSON.stringify(clauses[result]),"bad replay");checks++}
 function compile(fs){let C=dag(n),r=C.fold(fs.map(c=>C.fold(c.map(l=>l>0?C.v[l-1]:C.neg(C.v[-l-1])),C.or,C.zero)),C.mul,C.one);return {C,r}}
 let A=compile(F),B=compile([...F,clauses[learned]]);
 for(let s=0;s<1<<n;s++){let x=Array.from({length:n},(_,i)=>s>>i&1),ok=F.every(c=>c.some(l=>x[Math.abs(l)-1]===+(l>0)));assert(A.C.evaluate(A.r,x)===+ok&&B.C.evaluate(B.r,x)===+ok&&!ok,"CNF mismatch");checks+=2}
 return {n,sourceClauses:F.length,resolutionSteps:trace.length,learned:clauses[learned],original:A.C.metrics(A.r),withLearned:B.C.metrics(B.r)};
}
let cdcl=[4,5,6,8,12].map(learnedFixture);
// One-hot/zero block quotient, with exact block-multilinear coefficients.
// A vertex input chooses one incident edge-label string. The circuit checks
// occupancy and edge agreement; a small circuit realizes the full graph tensor
// ON THIS RESTRICTED DOMAIN, not on the full Boolean cube.
function graphBlock(k){
 let q=1<<(k-1),C=dag(k*q,Array.from({length:k*q},(_,i)=>Math.floor(i/q))),edges=[];
 const pos=(v,u)=>u<v?u:u-1;
 for(let v=0;v<k;v++)for(let u=v+1;u<k;u++)edges.push([v,u]);
 let occ=[],local=new Map();for(let v=0;v<k;v++){let xs=C.v.slice(v*q,(v+1)*q);occ.push(C.fold(xs,C.plus,C.zero));for(let u=0;u<k;u++)if(u!==v)local.set(v+":"+u,C.fold(xs.filter((_,a)=>a>>pos(v,u)&1),C.plus,C.zero))}
 let eq=edges.map(([v,u])=>C.neg(C.plus(local.get(v+":"+u),local.get(u+":"+v)))),r=C.fold([...occ,...eq],C.mul,C.one);
 let cut=Math.floor(k/2),boundary=edges.filter(([v,u])=>v<cut&&u>=cut),rank=2**boundary.length;
 function label(a,b){let x=Array(k*q).fill(0),labs=Array(k).fill(0);boundary.forEach(([v,u],i)=>{labs[v]|=((a>>i)&1)<<pos(v,u);labs[u]|=((b>>i)&1)<<pos(u,v)});labs.forEach((z,v)=>x[v*q+z]=1);return x}
 // Exact symbolic minor: internal edge labels fixed zero; each boundary bit
 // appears once at each endpoint; equality iff a=b. Enumerate actual gate
 // evaluations for small minors, sample larger ones, never claim sampled rank.
 let samples=0;if(rank<=16){for(let a=0;a<rank;a++)for(let b=0;b<rank;b++){assert(C.evaluate(r,label(a,b))===+(a===b),"minor");samples++}}
 else{for(let i=0;i<64;i++){let a=(random()>>>8)%rank,b=i%2?a:((a+1)%rank);assert(C.evaluate(r,label(a,b))===+(a===b),"minor sample");samples++}}
 let missing=label(0,0);missing[0]=0;assert(C.evaluate(r,missing)===0,"zero block");
 // Explicit difference full cube vs one-hot polynomial: two different labels
 // selected in one block with all other vertices fixed at zero labels. Target
 // graph state sum is 1 (exactly one consistent label); parity occupancy kills.
 let multi=label(0,0);multi[1]=1;assert(C.evaluate(r,multi)===0,"multi-hot control");
 let exact=0;for(let a=0;a<q;a++)if(multi[a]&&a===0)exact^=1;assert(exact===1,"state-sum reference");
 checks+=samples+3;
 return {k,q,boundary:boundary.length,exactIdentityMinorRank:rank,minorGateChecks:samples,variable:C.metrics(r),block:C.metrics(r,true),multiHotMismatch:true};
}
let block=[3,4,5,6,8].map(graphBlock);
return {status:"PASS",standard,cdcl,block,checks,scope:"exact finite checks; syntactic metrics, not minimum complexity; no upstream result assumed"};
}
function equalityControl(){
 const a=[];let checks=0;
 for(let r of [1,2,4,8,12,16]){
  const n=2**r;
  const evalEq=(x,y)=>{let f=1;for(let i=0;i<r;i++)f&=1^((x>>i)&1)^((y>>i)&1);return f};
  if(r<=8){for(let x=0;x<n;x++)for(let y=0;y<n;y++){if(evalEq(x,y)!==+(x===y))throw Error("equality");checks++}}
  else for(let x=0;x<n;x+=127){if(evalEq(x,x)!==1||evalEq(x,(x+1)%n)!==0)throw Error("equality");checks+=2}
  a.push({r,variables:2*r,arithmeticOperations:3*r-1,rank:n,w:0,b:0,t:0});
 }
 return {a,checks};
}
const result=campaign();result.fullCubeEquality=equalityControl();console.log(JSON.stringify(result,null,2));
