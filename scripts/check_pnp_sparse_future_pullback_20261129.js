// Section 48: sparse circuit-source Koopman closure with fail-closed resource caps.
function campaign(){
"use strict";
const assert=(x,m)=>{if(!x)throw Error(m)},range=n=>Array.from({length:n},(_,i)=>i),bit=i=>1n<<BigInt(i);
class Refusal extends Error{}
function compiler(n,actions,obs,limits){
 const stats={work:0,peakTerms:0,pullbacks:0,rank:0,coordinates:0};
 function pay(k=1){if(stats.work+k>limits.work)throw new Refusal("work");stats.work+=k}
 function toggle(s,x){pay();if(s.has(x))s.delete(x);else{s.add(x);if(s.size>limits.terms)throw new Refusal("terms");stats.peakTerms=Math.max(stats.peakTerms,s.size)}}
 const poly=xs=>{let s=new Set();for(let x of xs)toggle(s,x);return s};
 const plus=(a,b)=>poly([...a,...b]);
 function times(a,b){let s=new Set();for(let x of a)for(let y of b)toggle(s,x|y);return s}
 function fromDAG(gates,out){let v=[];function read(w){pay();assert(w[0]==="i"||w[0]==="g","wire type");assert(Number.isInteger(w[1])&&w[1]>=0&&w[1]<(w[0]==="i"?n:v.length),"wire range");return w[0]==="i"?poly([bit(w[1])]):v[w[1]]}
  for(let [op,args] of gates){pay();let r;if(op==="const")r=poly(args[0]?[0n]:[]);else if(op==="not")r=plus(poly([0n]),read(args[0]));else{let a=read(args[0]),b=read(args[1]);assert(["and","or","xor"].includes(op),"gate");r=op==="and"?times(a,b):op==="xor"?plus(a,b):plus(plus(a,b),times(a,b))}v.push(r)}
  return out.map(read);
 }
 function pull(p,sub){stats.pullbacks++;let sum=new Set();for(let m of p){pay();let f=poly([0n]),b=m;while(b){let lo=b&-b,i=lo.toString(2).length-1;pay();f=times(f,sub[i]);if(!f.size)break;b^=lo}for(let z of f)toggle(sum,z)}return sum}
 function pivot(s){let m=-1n;for(let x of s){pay();if(x>m)m=x}return m}
 const rows=[],basis=new Map(),images=[],coords=[];
 function reduce(p){let s=poly(p),c=0n;while(s.size){let m=pivot(s);if(!basis.has(m))break;let i=basis.get(m);s=plus(s,rows[i]);c^=bit(i)}return [s,c]}
 function insert(p){let [s]=reduce(p);if(!s.size)return;if(rows.length>=limits.rank)throw new Refusal("rank");basis.set(pivot(s),rows.length);rows.push(s);stats.rank=rows.length}
 function coordinate(p){let [s,c]=reduce(p);assert(!s.size,"not invariant");stats.coordinates++;return c}
 try{
  const T=actions.map(a=>fromDAG(a.gates,a.out)),O=fromDAG(obs.gates,obs.out);
  assert(T.every(t=>t.length===n),"transition arity");
  for(let p of O)insert(p);
  for(let i=0;i<rows.length;i++){let a=T.map(t=>pull(rows[i],t));images.push(a);for(let p of a)insert(p)}
  for(let a=0;a<T.length;a++)coords.push(images.map(z=>coordinate(z[a])));
  const obsCoords=O.map(coordinate);
  return {status:"EXACT",rows,coords,obsCoords,stats};
 }catch(e){if(e instanceof Refusal)return {status:"CENSORED",reason:e.message,stats};throw e}
}
const parity=x=>{let s=0n;while(x){s^=1n;x&=x-1n}return s};
const evaluate=(p,x)=>{let z=0n;for(let m of p)if((x&m)===m)z^=1n;return z};
const pack=(p,x)=>p.reduce((s,q,i)=>s|(evaluate(q,x)<<BigInt(i)),0n);
const lin=(M,x)=>M.reduce((s,r,i)=>s|(parity(r&x)<<BigInt(i)),0n);
function matmul(A,B){return A.map(r=>{let z=0n;for(let i=0;i<B.length;i++)if(r&bit(i))z^=B[i];return z})}
function jump(M,x,h){while(h){if(h&1n)x=lin(M,x);h>>=1n;if(h)M=matmul(M,M)}return x}
function actual(a,x){let v=[];const read=w=>w[0]==="i"?Number((x>>BigInt(w[1]))&1n):v[w[1]];for(let [op,args] of a.gates){let y=op==="const"?+args[0]:op==="not"?1-read(args[0]):op==="and"?read(args[0])&read(args[1]):op==="or"?read(args[0])|read(args[1]):read(args[0])^read(args[1]);v.push(y)}return a.out.reduce((s,w,i)=>s|(BigInt(read(w))<<BigInt(i)),0n)}
function partition(n,actions,obs){let N=1<<n,q=range(N).map(x=>actual(obs,BigInt(x)).toString());while(true){let m=new Map(),z=range(N).map(x=>{let k=JSON.stringify([q[x],...actions.map(a=>q[Number(actual(a,BigInt(x)))])]);if(!m.has(k))m.set(k,m.size);return m.get(k)});if(z.every((a,i)=>a===q[i]))return z;q=z}}
let seed=4801;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
let counts={random:0,pairs:0,squares:0,observations:0,jumps:0,largeSquares:0,largeJumps:0,degreeCollapse:0,refusals:0,costedMaps:0,costedSteps:0,costedConsumers:0};
const I=i=>["i",i],G=i=>["g",i],lim={rank:128,terms:2048,work:2000000};
// Produce actual const/not/and/or DAGs, sharing monomials once.
 // XOR is lowered to (a OR b) AND NOT(a AND b), four actual gate events.
 function paidDAG(rows){
 let gates=[],cache=new Map();
 const emit=(op,args)=>{let j=gates.length;gates.push([op,args]);return G(j)};
 const xor=(a,b)=>emit("and",[emit("or",[a,b]),emit("not",[emit("and",[a,b])])]);
 function mono(m){if(cache.has(m))return cache.get(m);let a;if(m===0n)a=emit("const",[true]);else{let lo=m&-m,j=lo.toString(2).length-1;a=m===lo?I(j):emit("and",[mono(m^lo),I(j)])}cache.set(m,a);return a}
 const out=rows.map(p=>{let a;for(let m of p){let b=mono(m);a=a===undefined?b:xor(a,b)}return a===undefined?emit("const",[false]):a});
 return {gates,out};
 }
 const linearDAG=M=>paidDAG(M.map(r=>{let p=new Set();while(r){let lo=r&-r;p.add(lo);r^=lo}return p}));
 function costs(R){return {map:paidDAG(R.rows),steps:R.coords.map(linearDAG),consumer:linearDAG(R.obsCoords)}}
 function checkPaid(P,R,x,a,next,obs){let c=actual(P.map,x);assert(c===pack(R.rows,x),"paid map");counts.costedMaps++;
 assert(actual(P.steps[a],c)===pack(R.rows,next),"paid step");counts.costedSteps++;
 assert(actual(P.consumer,c)===obs,"paid consumer");counts.costedConsumers++}
 function make(n){let gates=[],w=range(n).map(I);for(let j=0;j<8;j++){let op=["not","and","or","xor","const"][rnd(5)],a=op==="const"?[!!rnd(2)]:op==="not"?[w[rnd(w.length)]]:[w[rnd(w.length)],w[rnd(w.length)]];gates.push([op,a]);w.push(G(j))}return {gates,out:range(n).map(()=>w[rnd(w.length)])}}
for(let k=0;k<64;k++){let n=2+rnd(5),N=1<<n,A=1+rnd(3),actions=range(A).map(()=>make(n)),obs={gates:[],out:[I(rnd(n))]},R=compiler(n,actions,obs,lim);assert(R.status==="EXACT","small closure");let P=costs(R),q=partition(n,actions,obs),codes=range(N).map(x=>pack(R.rows,BigInt(x)));
 for(let x=0;x<N;x++){assert(lin(R.obsCoords,codes[x])===actual(obs,BigInt(x)),"observation");counts.observations++;for(let a=0;a<A;a++){assert(lin(R.coords[a],codes[x])===codes[Number(actual(actions[a],BigInt(x)))],"square");counts.squares++;checkPaid(P,R,BigInt(x),a,actual(actions[a],BigInt(x)),actual(obs,BigInt(x)))}for(let y=x;y<N;y++){assert((codes[x]===codes[y])===(q[x]===q[y]),"minimal");counts.pairs++}}
 for(let j=0;j<4;j++){let a=rnd(A),x=BigInt(rnd(N)),h=1+rnd(32),z=x;for(let i=0;i<h;i++)z=actual(actions[a],z);assert(jump(R.coords[a],pack(R.rows,x),BigInt(h))===pack(R.rows,z),"jump");counts.jumps++}counts.random++;
}
// Actual circuit ABI, nonlinear cyclic shift with a fixed quadratic control.
// t'_i=t_(i+1) xor (c*d), c,d fixed. Code span t_i and c*d.
// No truth table or explicit state enumeration is used for this family.
let large=[];
for(let m of [4,8,16,32,64,128,256]){
 let n=m+2,gates=[["and",[I(m),I(m+1)]]];for(let i=0;i<m;i++)gates.push(["xor",[I((i+1)%m),G(0)]]);
 let a={gates,out:[...range(m).map(i=>G(i+1)),I(m),I(m+1)]},o={gates:[],out:[I(0)]};
 let R=compiler(n,[a],o,{rank:m+2,terms:8,work:4000000});assert(R.status==="EXACT"&&R.rows.length===m,"sparse cyclic closure");let P=costs(R);
 // The orbit of t0 contains t_i plus parity(i)*cd, and for even m
 // the phase closes. It never needs the separate quadratic observable.
 for(let j=0;j<16;j++){let x=range(n).reduce((s,i)=>s|(BigInt(rnd(2))<<BigInt(i)),0n),c=pack(R.rows,x);assert(lin(R.coords[0],c)===pack(R.rows,actual(a,x)),"large square");counts.largeSquares++;checkPaid(P,R,x,0,actual(a,x),actual(o,x));
 let h=(1n<<80n)+BigInt(12345+j),d=h%BigInt(m),mask=bit(m)-1n,t=x&mask,rotate=((t>>d)|(t<<(BigInt(m)-d)))&mask,cd=((x>>BigInt(m))&1n)*((x>>BigInt(m+1))&1n);if((h&1n)&&cd)rotate^=mask;let z=(x&~mask)|rotate;
 assert(jump(R.coords[0],c,h)===pack(R.rows,z),"large jump");counts.largeJumps++}
 large.push({stateBits:n,rank:R.rows.length,peakTerms:R.stats.peakTerms,work:R.stats.work,gateCount:gates.length,paidMapGates:P.map.gates.length,paidStepGates:P.steps[0].gates.length,paidConsumerGates:P.consumer.gates.length,explicitStates:"2^"+n});
}
let collapse=compiler(2,[{gates:[],out:[I(0),I(0)]}],{gates:[["and",[I(0),I(1)]]],out:[G(0)]},lim);assert(collapse.status==="EXACT"&&collapse.rows.length===2&&collapse.rows.some(p=>p.has(1n)),"degree collapse");counts.degreeCollapse++;
for(let limits of [{rank:0,terms:20,work:1000},{rank:20,terms:0,work:1000},{rank:20,terms:20,work:1}]){let r=compiler(2,[{gates:[],out:[I(1),I(0)]}],{gates:[],out:[I(0)]},limits);assert(r.status==="CENSORED"&&!r.rows,"fail closed");counts.refusals++}
// Dense expansion control: product of independent OR pairs has 3^m
 // ANF terms despite a linear-sized gate description. Refuse, do not truncate.
 let gates=[],m=12;for(let i=0;i<m;i++)gates.push(["or",[I(2*i),I(2*i+1)]]);
 let w=G(0);for(let i=1;i<m;i++){gates.push(["and",[w,G(i)]]);w=G(gates.length-1)}
 let dense=compiler(2*m,[{gates:[],out:range(2*m).map(I)}],{gates,out:[w]},{rank:128,terms:1024,work:2000000});
 assert(dense.status==="CENSORED"&&dense.reason==="terms","dense refusal");counts.refusals++;
 return {status:"PASS",seed:4801,denseControl:{gates:gates.length,exactTerms:"531441",status:dense.status,stats:dense.stats},counts,large,scope:"exact sparse GF2 pullback on circuit descriptions; operation caps not calibrated bit-TM clocks; no universal polynomial bound"};
}
console.log(JSON.stringify(campaign(),null,2));
