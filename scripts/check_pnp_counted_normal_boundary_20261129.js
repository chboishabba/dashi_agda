// Section50 counted intrinsic normal-space boundary join, exact finite referee.
function campaign(){
"use strict";
const assert=(x,m)=>{if(!x)throw Error(m)},seq=n=>Array.from({length:n},(_,i)=>i),bit=i=>1n<<BigInt(i);
const pop=x=>{let c=0;while(x){x&=x-1n;c++}return c},dot=(x,y)=>pop(x&y)&1;
class Refusal extends Error{}
function solve(n,source,queries,lim,clip=null){
 let stats={work:0,joins:0,compatible:0,width:0,peakTable:0,treeCandidates:0,queries:0,countBitOps:0};
 function pay(k=1){if(stats.work+k>lim.work)throw new Refusal("work");stats.work+=k}
 function mul(a,b){let k=a.toString(2).length*b.toString(2).length;pay(k);stats.countBitOps+=k;let v=a*b;return clip===null?v:v>clip?clip:v}
 function add(a,b){let k=Math.max(a.toString(2).length,b.toString(2).length);pay(k);stats.countBitOps+=k;let v=a+b;return clip===null?v:v>clip?clip:v}
 function pow(k){pay(k+1);return clip===null?bit(k):bit(k)>clip?clip:bit(k)}
 // Echelon equations, with original normals and exact right-hand bits.
 function canon(R){let B=new Map();for(let [a,b] of R){assert(typeof a==="bigint"&&a>=0n&&(a>>BigInt(n))===0n&&(b===0||b===1),"source row");while(a){pay(n+1);let p=a.toString(2).length-1;if(B.has(p)){let [u,v]=B.get(p);a^=u;b^=v}else{B.set(p,[a,b]);break}}if(!a&&b)return null}return [...B.values()].sort((a,b)=>a[0]<b[0]?-1:1)}
 const span=A=>canon(A.map(a=>[a,0])).map(r=>r[0]);
 function rep(R){let x=0n;for(let [a,b] of R){pay(n+1);if(dot(a,x)!==b)x|=bit(a.toString(2).length-1)}return x}
 function orth(A){let R=canon(A.map(a=>[a,0])),p=new Set(R.map(([a])=>a.toString(2).length-1)),V=[];for(let i=0;i<n;i++)if(!p.has(i)){let x=bit(i);for(let [a] of R){pay(n+1);if(dot(a,x))x|=bit(a.toString(2).length-1)}V.push(x)}return span(V)}
 const inter=(A,B)=>orth(span([...orth(A),...orth(B)]));
 function val(A,x){pay((n+1)*(A.length+1));return A.reduce((s,a,i)=>s|(BigInt(dot(a,x))<<BigInt(i)),0n)}
 const eq=(A,v)=>A.map((a,i)=>[a,Number((v>>BigInt(i))&1n)]);
 function node(mask,U,D,l=null,r=null,leaf=null){return {mask,U,D,l,r,leaf}}
 function prepare(L){
 let m=L.length; if(!m)return null;let full=bit(m)-1n,space=new Map(),bounds=new Map(),A=L.map(f=>span(f.rows.map(r=>r[0])));
 function U(mask){if(!space.has(mask)){let a=[];for(let j=0;j<m;j++){pay();if(mask&bit(j))a.push(...A[j])}space.set(mask,span(a))}return space.get(mask)}
 function D(mask){if(!bounds.has(mask))bounds.set(mask,inter(U(mask),U(full^mask)));return bounds.get(mask)}
 let nodes=L.map((f,i)=>node(bit(i),A[i],D(bit(i)),null,null,f));
 while(nodes.length>1){let best=null;for(let i=0;i<nodes.length;i++)for(let j=i+1;j<nodes.length;j++){pay();stats.treeCandidates++;let mask=nodes[i].mask|nodes[j].mask,d=D(mask).length;let score=[d,pop(mask),i,j];if(best===null||score[0]<best[0]||score[0]===best[0]&&score[1]<best[1])best=score}
 let [d,sz,i,j]=best,l=nodes[i],r=nodes[j],mask=l.mask|r.mask;nodes.splice(j,1);nodes.splice(i,1);nodes.push(node(mask,U(mask),D(mask),l,r))}
 return nodes[0]
 }
 function valid(x,L){return L.every(f=>{let k=f.rows.filter(([a,b])=>dot(a,x)===b).length;return f.kind==="forbid"?k!==f.rows.length:f.kind==="require"?k===f.rows.length:k===1})}
 function run(root){
 if(!root)return {count:pow(n),witness:0n};
 function fold(t){
 let d=t.D.length;stats.width=Math.max(stats.width,d);if(d>lim.width)throw new Refusal("width");let T=new Map();
 function put(key,c,x){if(!c)return;pay();if(!T.has(key))T.set(key,{count:c,x});else T.get(key).count=add(T.get(key).count,c);stats.peakTable=Math.max(stats.peakTable,T.size)}
 if(t.leaf){
 let f=t.leaf,rank=t.U.length;
 if(f.kind==="onehot"||f.kind==="require"){
 let patterns=f.kind==="require"?[f.rows]:f.rows.map((_,j)=>f.rows.map(([a,b],i)=>[a,b^Number(i!==j)]));
 // Distinct bit patterns give distinct functionals on U, even dependent normals.
 let seen=new Set();for(let pat of patterns){pay();let R=canon(pat);if(R===null)continue;let x=rep(R),v=val(t.U,x);if(seen.has(v))continue;seen.add(v);put(val(t.D,x),1n,x)}
 }else{
 let bad=canon(f.rows),badX=bad===null?null:rep(bad),badD=badX===null?null:val(t.D,badX);
 // A forbidden flat excludes exactly one functional on its full normal span.
 // Compute unclipped cardinal minus one FIRST, then clip.
 for(let k=0n;k<bit(d);k++){pay();let c=bit(rank-d)-(badD===k?1n:0n);if(!c)continue;let pins=canon(eq(t.D,k)),x=rep(pins);
 if(bad!==null&&f.rows.every(([a,b])=>dot(a,x)===b)){
 let v=orth(t.D).find(y=>t.U.some(a=>dot(a,y)));assert(v!==undefined,"leaf escape");x^=v
 }
 assert(valid(x,[f]),"leaf");put(k,clip===null?c:c>clip?clip:c,x)}
 }
 return T
 }
 let L=fold(t.l),R=fold(t.r),I=inter(t.l.U,t.r.U),bins=new Map();
 for(let e of R.values()){let k=val(I,e.x);if(!bins.has(k))bins.set(k,[]);bins.get(k).push(e)}
 for(let l of L.values()){let k=val(I,l.x);for(let r of bins.get(k)||[]){pay();stats.joins++;let H=canon([...eq(t.l.U,val(t.l.U,l.x)),...eq(t.r.U,val(t.r.U,r.x))]);assert(H!==null,"gluing");let x=rep(H);put(val(t.D,x),mul(l.count,r.count),x);stats.compatible++}}
 return T
 }
 let T=fold(root),q=T.get(0n);return q?{count:mul(q.count,pow(n-root.U.length)),witness:q.x}:{count:0n,witness:null}
 }
 try{
 assert(clip===null||clip>=1n,"clip");assert(source.every(f=>["forbid","require","onehot"].includes(f.kind)),"kind");pay(1+n+source.reduce((s,f)=>s+1+f.rows.length,0));
 let base=run(prepare(source));assert(base.witness===null||valid(base.witness,source),"original witness");
 let children=[];for(let a of queries){let c=[];for(let b=0;b<2;b++){stats.queries++;let L=[...source,{kind:"require",rows:[[a,b]]}],q=run(prepare(L));assert(q.witness===null||valid(q.witness,L),"conditional witness");c.push(q)}assert(add(c[0].count,c[1].count)===base.count,"parent conservation");children.push(c)}
 return {status:"EXACT",base,children,stats};
 }catch(e){if(e instanceof Refusal)return {status:"CENSORED",reason:e.message,stats};throw e}
}
let seed=5001;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
let counts={cases:0,counts:0,conditional:0,witnesses:0,clip:0,refusals:0};
const lim={work:30000000,width:12};
function valid(x,S){return S.every(f=>{let k=f.rows.filter(([a,b])=>dot(a,x)===b).length;return f.kind==="forbid"?k!==f.rows.length:f.kind==="require"?k===f.rows.length:k===1})}
for(let i=0;i<128;i++){let n=1+rnd(7),S=seq(rnd(7)).map(()=>({kind:["forbid","require","onehot"][rnd(3)],rows:seq(rnd(4)).map(()=>[BigInt(rnd(2**n)),rnd(2)])})),Q=seq(n).map(bit),truth=seq(2**n).map(BigInt).filter(x=>valid(x,S));
 let r=solve(n,S,Q,lim);assert(r.status==="EXACT"&&r.base.count===BigInt(truth.length),"count");counts.counts++;
 if(truth.length){assert(truth.includes(r.base.witness),"reopen");counts.witnesses++}
 for(let j=0;j<n;j++)for(let b=0;b<2;b++){let a=truth.filter(x=>dot(Q[j],x)===b),z=r.children[j][b];assert(z.count===BigInt(a.length),"conditional");if(a.length){assert(a.includes(z.witness),"conditional reopen");counts.witnesses++}counts.conditional++}
 let c=solve(n,S,[],lim,2n);assert(c.status==="EXACT"&&c.base.count===BigInt(Math.min(2,truth.length)),"clipped");counts.clip++;counts.cases++;
}
// High local rank, small boundary. One forbidden point is not enumerated.
let big=solve(128,[{kind:"forbid",rows:seq(128).map(j=>[bit(j),0])}], [bit(0),bit(127)],{work:30000000,width:4});assert(big.status==="EXACT"&&big.base.count===bit(128)-1n&&big.children[0][0].count===bit(127)-1n&&big.children[0][1].count===bit(127),"high rank");
let refused=solve(3,[{kind:"forbid",rows:[[1n,0],[2n,1]]},{kind:"forbid",rows:[[1n,1],[4n,0]]}],[],{work:100000,width:0});assert(refused.status==="CENSORED"&&!refused.base,"width");counts.refusals++;
let cap=solve(4,[],[1n],{work:1,width:4});assert(cap.status==="CENSORED"&&!cap.base,"work");counts.refusals++;
const original=[[2,10,15],[7,9,12],[3,4,14],[0,6,16],[1,5,13],[8,11,17],[9,15,16],[0,8,14],[2,6,17],[5,10,13],[1,3,12],[4,7,11],[3,11,12],[1,2,6],[0,7,14],[4,9,15],[10,13,17],[5,8,16],[0,1,14],[4,9,16],[7,12,15],[2,5,17],[3,6,11],[8,10,13],[0,1,9],[4,11,17],[3,6,16],[2,10,12],[5,14,15],[7,8,13]];
// Work on original parity chart: equation sum each exact-one row mod 2 =1.
// Derive chart locally, preserving original coordinates as linear forms.
function chart(n,R){let B=new Map();for(let [a,b] of R){while(a){let p=a.toString(2).length-1;if(B.has(p)){let [u,v]=B.get(p);a^=u;b^=v}else{B.set(p,[a,b]);break}}assert(a||!b,"chart inconsistent")}
 let E=[...B.values()].sort((a,b)=>a[0]<b[0]?-1:1),P=new Set(E.map(([a])=>a.toString(2).length-1));function lift(x,hom){for(let [a,b] of E)if(dot(a,x)!==(hom?0:b))x^=bit(a.toString(2).length-1);return x}
 return {u:lift(0n,false),V:seq(n).filter(i=>!P.has(i)).map(i=>lift(bit(i),true))}}
let R=seq(18).map(i=>original.reduce((m,S,j)=>S.includes(i)?m|bit(j):m,0n)),{u,V}=chart(30,R.map(a=>[a,1]));
let forms=seq(30).map(i=>V.reduce((a,v,j)=>v&bit(i)?a|bit(j):a,0n));
let S=seq(18).map(i=>({kind:"onehot",rows:seq(30).filter(j=>R[i]&bit(j)).map(j=>[forms[j],1^Number((u>>BigInt(j))&1n)])}));
let orig=solve(V.length,S,[],{work:200000000,width:14});assert(orig.status==="EXACT"&&orig.base.count===7n,"original count");
let lift=z=>V.reduce((a,v,j)=>z&bit(j)?a^v:a,u),w=lift(orig.base.witness);
assert(R.every(a=>pop(a&w)===1),"original lift");
let direct=[];function covers(mask,x){if(mask===bit(18)-1n){direct.push(x);return}let j=0;while(mask&bit(j))j++;for(let i=0;i<30;i++){let a=original[i].reduce((m,k)=>m|bit(k),0n);if(a&bit(j)&&!(a&mask))covers(mask|a,x|bit(i))}}
covers(0n,0n);assert(direct.length===7&&direct.includes(w),"independent original");
let conditional=[];for(let j=0;j<30;j++){let q=solve(V.length,S,[forms[j]],{work:200000000,width:14});assert(q.status==="EXACT","original conditional");let p=Number((u>>BigInt(j))&1n);let a=[q.children[0][p],q.children[0][p^1]];for(let b=0;b<2;b++){assert(a[b].count===BigInt(direct.filter(x=>Number((x>>BigInt(j))&1n)===b).length),"original bit");if(a[b].count)assert(direct.includes(lift(a[b].witness))&&Number((lift(a[b].witness)>>BigInt(j))&1n)===b,"original conditional lift");counts.conditional++}conditional.push({column:j,counts:a.map(z=>String(z.count)),work:q.stats.work})}
return {status:"PASS",counts,highRank:{count:String(big.base.count),stats:big.stats},original:{chartDimension:V.length,count:String(orig.base.count),witness:String(w),stats:orig.stats,conditional,conditionalWork:conditional.reduce((a,x)=>a+x.work,0)},scope:"exact finite counted normal-boundary join, caps not physical clocks; no unrestricted width claim"};
}
console.log(JSON.stringify(campaign(),null,2));
