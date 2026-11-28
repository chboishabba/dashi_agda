// Section47 exact finite nonlinear, clocked and Fourier incidence controls.
function campaign(){
"use strict";
const assert=(x,m)=>{if(!x)throw Error(m)},range=n=>Array.from({length:n},(_,i)=>i);
let seed=4701;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
const counts={nonlinearPairs:0,nonlinearSquares:0,defectReplays:0,clockedPrefixes:0,clockedWitnesses:0,nsPairDerivatives:0,nsBuckets:0,nsRadicalReopens:0};
const parity=x=>{let y=0n;while(x){y^=1n;x&=x-1n}return y};
function mobius(v,n){let a=v.slice();for(let j=0;j<n;j++)for(let m=0;m<a.length;m++)if(m&(1<<j))a[m]^=a[m^(1<<j)];return a.reduce((r,x,i)=>r|(BigInt(x)<<BigInt(i)),0n)}
function value(p,x){let a=0;for(let s=x;;s=(s-1)&x){a^=Number((p>>BigInt(s))&1n);if(!s)return a}}
function closure(n,T,obs,cap){
 let N=1<<n,B=new Map(),rows=[],work=0;
 function insert(v){while(v){let p=v.toString(2).length-1;if(B.has(p))v^=B.get(p);else{if(rows.length===cap)return false;B.set(p,v);rows.push(v);return true}}return true}
 for(let o of obs)if(!insert(o))return {status:"CENSORED",rank:rows.length,work};
 for(let i=0;i<rows.length;i++)for(let t of T){let p=mobius(range(N).map(x=>value(rows[i],t[x])),n);work+=N;if(!insert(p))return {status:"CENSORED",rank:rows.length,work}}
 const code=x=>rows.map(r=>value(r,x)).join("");
 return {status:"EXACT",rank:rows.length,work,code,rows};
}
let nonlinear=[];for(let k=0;k<48;k++){let n=2+rnd(4),N=1<<n,A=1+rnd(2),T=range(A).map(()=>range(N).map(()=>rnd(N))),obs=[2n];let L=closure(n,T,obs,N);
 assert(L.status==="EXACT","full rank cap");
 let q=range(N).map(x=>value(obs[0],x));
 while(true){let keys=new Map(),z=range(N).map(x=>{let s=JSON.stringify([q[x],...T.map(t=>q[t[x]])]);if(!keys.has(s))keys.set(s,keys.size);return keys.get(s)});if(z.every((v,i)=>v===q[i]))break;q=z}
 for(let x=0;x<N;x++)for(let y=x;y<N;y++){assert((q[x]===q[y])===(L.code(x)===L.code(y)),"nonlinear span vs partition");counts.nonlinearPairs++}
 for(let t of T){let map=new Map();for(let x=0;x<N;x++){let a=L.code(x),b=L.code(t[x]);assert(!map.has(a)||map.get(a)===b,"nonlinear successor");map.set(a,b);counts.nonlinearSquares++}}
 nonlinear.push({n,rank:L.rank,classes:new Set(q).size,pullbackPointEvaluations:L.work});
}
let censor=closure(5,[range(32).map(x=>(x+1)%32)],[mobius(range(32).map(x=>+(x===0)),5)],4);assert(censor.status==="CENSORED","cap refusal");
let xy=8n,substitution=[0,3,0,3],pull=mobius(range(4).map(x=>value(xy,substitution[x])),2);assert(pull===2n,"x*y -> x");
for(let k=0;k<100;k++){let n=2+rnd(5),N=1<<n,M=range(n).map(()=>BigInt(rnd(N))),b=BigInt(rnd(N)),x=BigInt(rnd(N)),z=x;
 const linear=y=>M.reduce((a,r,i)=>a|(parity(r&y)<<BigInt(i)),0n),aff=y=>linear(y)^b;
 const nonlinear=y=>aff(y)^(((y&1n)&&((y>>1n)&1n))?4n%BigInt(N):0n);
 for(let j=0;j<16;j++){let d=nonlinear(x)^aff(x),e=x^z,xx=nonlinear(x),zz=aff(z);assert((xx^zz)===(d^linear(e)),"hybrid residual");x=xx;z=zz;counts.defectReplays++}
}
function run(F,x,budget){let used=0;for(let C of F){let ok=false;for(let l of C){if(used===budget)return {kind:"timeout",used};used++;if(((x>>(Math.abs(l)-1))&1)===+(l>0)){ok=true;break}}if(!ok)return {kind:"reject",used}}return {kind:"accept",used}}
for(let k=0;k<100;k++){let n=2+rnd(6),N=1<<n,F=range(1+rnd(8)).map(()=>range(1+rnd(3)).map(()=> (1+rnd(n))*(rnd(2)?1:-1))),T=F.reduce((s,c)=>s+c.length,0),truth=[];
 for(let x=0;x<N;x++){let exact=F.every(c=>c.some(l=>((x>>(Math.abs(l)-1))&1)===+(l>0))),r=run(F,x,T);assert(r.kind!=="timeout"&&(r.kind==="accept")===exact&&r.used<=T,"clock verifier");truth.push(exact);counts.clockedWitnesses++;
  for(let h=0;h<=T;h++){let a=run(F,x,h);assert(a.used<=h&&(a.kind==="timeout"||a.kind===r.kind),"bounded prefix");counts.clockedPrefixes++}
 }
 assert(truth.some(Boolean)===range(N).some(x=>run(F,x,T).kind==="accept"),"finite SAT consumer")
}
const C=1,modes=[];for(let i=-C;i<=C;i++)for(let j=-C;j<=C;j++)for(let k=-C;k<=C;k++)modes.push([i,j,k]);
const key=v=>v.join(","),dot=(a,b)=>a.reduce((z,x,i)=>z+x*b[i],0),add=(a,b)=>a.map((x,i)=>x+b[i]),sub=(a,b)=>a.map((x,i)=>x-b[i]),scale=(a,k)=>a.map(x=>x*k),neg=a=>scale(a,-1),norm=a=>dot(a,a),cross=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]],tensor=(a,b)=>a.flatMap(x=>b.map(y=>x*y));
const Z=()=>Array(9).fill(0),D=6;let leakage=0;
for(let trial=0;trial<18;trial++){
 let U=new Map();for(let p of modes){if(U.has(key(p)))continue;let v=norm(p)?cross(p,range(3).map(()=>rnd(7)-3)):[0,0,0];U.set(key(p),v);U.set(key(neg(p)),v)}
 let N=new Map();for(let k of modes){let g=[0,0,0];for(let p of modes){let q=sub(k,p);if(U.has(key(q)))g=add(g,scale(U.get(key(q)),dot(U.get(key(p)),q)))}
 let r=norm(k),v=r?scale(sub(scale(g,r),scale(k,dot(k,g))),-D/r):[0,0,0];assert(v.every(Number.isSafeInteger)&&dot(k,v)===0,"Leray exact");N.set(key(k),v)}
 for(let k of [[1,0,0],[1,1,0],[0,0,1]]){
 let buckets=new Map(),rows=[];
 for(let p of modes){let q=sub(k,p);if(!U.has(key(q)))continue;let a=U.get(key(p)),b=U.get(key(q)),r=norm(p)+norm(q),d=tensor(a,b),j=add(tensor(N.get(key(p)),b),tensor(a,N.get(key(q))));
 // Independent finite difference of the polynomial product, extracting odd part at +/-1.
 let plus=tensor(add(scale(a,D),N.get(key(p))),add(scale(b,D),N.get(key(q))));
 let minus=tensor(sub(scale(a,D),N.get(key(p))),sub(scale(b,D),N.get(key(q))));
 assert(key(sub(plus,minus))===key(scale(j,2*D)),"product derivative");counts.nsPairDerivatives+=9;
 rows.push({r,d,j});let g=buckets.get(r)||{d:Z(),j:Z(),n:0};g.d=add(g.d,d);g.j=add(g.j,j);g.n++;buckets.set(r,g)}
 for(let [r,g] of buckets){let direct=rows.filter(x=>x.r===r).reduce((z,x)=>add(z,x.j),Z());assert(key(direct)===key(g.j),"bucket forcing derivative");
 let damping=rows.filter(x=>x.r===r).reduce((z,x)=>add(z,scale(x.d,-r)),Z());assert(key(damping)===key(scale(g.d,-r)),"rate damping commutes");counts.nsBuckets++;
 for(let x of rows.filter(x=>x.r===r)){let residual=sub(scale(x.d,g.n),g.d);assert(key(add(residual,g.d))===key(scale(x.d,g.n)),"scaled reopen");counts.nsRadicalReopens++}
 if(g.j.some(x=>x!==0))leakage++;
 }
 }
}
return {status:"PASS",counts,nonlinearCases:nonlinear.length,cap:censor,rankRange:[Math.min(...nonlinear.map(x=>x.rank)),Math.max(...nonlinear.map(x=>x.rank))],nonzeroBucketNonlinearForcing:leakage,scope:"finite exact Boolean pullback (explicit cube cost), bounded verifier and original Fourier pair derivative at instantaneous rational data; not a physical trajectory or Clay theorem"};
}
console.log(JSON.stringify(campaign(),null,2));
