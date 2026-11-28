// NS–PNP dynamic-observation executable adapter. Node.js, no dependencies.
function campaign(){
"use strict";
const assert=(x,m)=>{if(!x)throw Error(m)},key=x=>JSON.stringify(x),seq=n=>Array.from({length:n},(_,i)=>i);
const ledger={stableSquares:0,pairReferees:0,separatorReplays:0,traceReplays:0,exactReopens:0,linearPairs:0,linearSquares:0,defectChecks:0,dagChecks:0};
let seed=4601;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
// Explicit finite, deterministic partial action graph. null = disabled,
// [successor,cost] = enabled. Costs are observed only when requested.
function quotient(G,observeCost=true){
 const {obs,edges}=G,N=obs.length,A=edges[0].length;
 assert(N>0&&edges.length===N&&edges.every(es=>es.length===A&&es.every(e=>e===null||(Number.isInteger(e[0])&&e[0]>=0&&e[0]<N&&Number.isSafeInteger(e[1])&&e[1]>=0))),"invalid graph");
 const classify=xs=>{let d=new Map();return xs.map(x=>{let k=key(x);if(!d.has(k))d.set(k,d.size);return d.get(k)})};
 let q=classify(obs),rounds=0,signatures=N;
 while(true){let z=classify(seq(N).map(s=>[q[s],...edges[s].map(e=>e===null?null:observeCost?[q[e[0]],e[1]]:[q[e[0]]])]));
  signatures+=N;rounds++;
  if(z.every((x,i)=>x===q[i]))break;q=z;
 }
 const reps=[],res=[],members=[];for(let s=0;s<N;s++){let c=q[s];if(!members[c]){members[c]=[];reps[c]=s}res[s]=members[c].length;members[c].push(s)}
 let reduced={obs:reps.map(s=>obs[s]),edges:reps.map(s=>edges[s].map(e=>e===null?null:[q[e[0]],observeCost?e[1]:0]))};
 for(let s=0;s<N;s++){assert(key(obs[s])===key(reduced.obs[q[s]]),"obs square");assert(members[q[s]][res[s]]===s,"exact reopening");ledger.exactReopens++;
  for(let a=0;a<A;a++){let e=edges[s][a],f=reduced.edges[q[s]][a];assert((e===null)===(f===null),"enable square");if(e)assert(q[e[0]]===f[0]&&(!observeCost||e[1]===f[1]),"successor square");ledger.stableSquares++}
 }
 return {q,reduced,members,res,rounds,signatures,classes:reps.length};
}
// Independent BFS on product graph returns shortest distinguishing word,
// including final observation, action enabledness and per-step cost.
function distinguish(G,s,t,cost){
 let todo=[[s,t,[]]],seen=new Set();for(let i=0;i<todo.length;i++){let [u,v,w,kind]=todo[i];if(kind)return {word:w,kind};let k=u+":"+v;if(seen.has(k))continue;seen.add(k);
  if(key(G.obs[u])!==key(G.obs[v]))return {word:w,kind:"observation"};
  for(let a=0;a<G.edges[u].length;a++){let e=G.edges[u][a],f=G.edges[v][a];if((e===null)!==(f===null)){todo.push([u,v,[...w,a],"enablement"]);continue}
   if(e&&f){if(cost&&e[1]!==f[1]){todo.push([u,v,[...w,a],"cost"]);continue}todo.push([e[0],f[0],[...w,a]])}
  }
 }return null;
}
function trace(G,s,w,cost){let out=[["obs",G.obs[s]]];for(let a of w){let e=G.edges[s][a];if(e===null){out.push(["disabled",a]);return out}if(cost)out.push(["cost",e[1]]);s=e[0];out.push(["obs",G.obs[s]])}return out}
function verify(G,cost=true,allPairs=true){
 let Q=quotient(G,cost),N=G.obs.length,A=G.edges[0].length,maxWord=0;
 if(allPairs)for(let s=0;s<N;s++)for(let t=s;t<N;t++){let d=distinguish(G,s,t,cost);assert((d===null)===(Q.q[s]===Q.q[t]),"independent product referee");ledger.pairReferees++;if(d){assert(key(trace(G,s,d.word,cost))!==key(trace(G,t,d.word,cost)),"separator replay");ledger.separatorReplays++;maxWord=Math.max(maxWord,d.word.length)}}
 for(let k=0;k<80;k++){let s=rnd(N),w=seq(20).map(()=>rnd(A));assert(key(trace(G,s,w,cost))===key(trace(Q.reduced,Q.q[s],w,cost)),"trace");ledger.traceReplays++}
 return {states:N,classes:Q.classes,rounds:Q.rounds,signatureRows:Q.signatures,maxWord:allPairs?maxWord:null};
}
let random=[];for(let k=0;k<100;k++){let N=2+rnd(18),A=1+rnd(4),G={obs:seq(N).map(()=>rnd(3)),edges:seq(N).map(()=>seq(A).map(()=>rnd(5)===0?null:[rnd(N),rnd(4)]))};random.push(verify(G,false),verify(G,true))}
const costG={obs:[0,0,1],edges:[[[2,1]],[[2,7]],[null]]};
assert(quotient(costG,false).classes===2&&quotient(costG,true).classes===3,"cost hiding");
const disabledG={obs:[0,0],edges:[[null],[[1,0]]]};assert(quotient(disabledG).classes===2,"admissibility hiding");
let counters=[];for(let n of [2,3,4,5,6,7,8,9]){let N=2**n,G={obs:seq(N).map(s=>+(s===0)),edges:seq(N).map(s=>[[(s+1)%N,1]])};
 let r=verify(G,true,n<=5);assert(r.classes===N,"counter must separate");let x=N-1;for(let j=0;j<12345;j++)x=G.edges[x][0][0];assert(x===(N-1+12345)%N,"jump arithmetic");counters.push({bits:n,...r,jump:"(state+horizon) mod 2^n",largestShortestSeparator:N-2})}
// Affine F2 action dynamics on a compact bit state. A row is a bit mask.
// Symbolic row saturation computes span of all O A_word, not state tables.
const parity=x=>{let b=0n;while(x){b^=1n;x&=x-1n}return b};
const dot=(r,x)=>parity(r&x);
function basis(){let rows=new Map();return {rows,insert(r){while(r){let p=r.toString(2).length-1;if(rows.has(p))r^=rows.get(p);else{rows.set(p,r);return r}}return 0n},contains(r){while(r){let p=r.toString(2).length-1;if(!rows.has(p))return false;r^=rows.get(p)}return true}}}
function pull(r,M){let z=0n;for(let i=0;i<M.length;i++)if((r>>BigInt(i))&1n)z^=M[i];return z}
function apply(M,x,b=0n){let z=b;for(let i=0;i<M.length;i++)z^=dot(M[i],x)<<BigInt(i);return z}
function linearClosure(n,actions,O){
 let B=basis(),agenda=[],ops=0;for(let r of O){let q=B.insert(r);if(q)agenda.push(q)}
 for(let i=0;i<agenda.length;i++)for(let {M} of actions){let r=B.insert(pull(agenda[i],M));ops++;if(r)agenda.push(r)}
 assert(agenda.length<=n&&O.every(r=>B.contains(r)),"span");for(let r of agenda)for(let {M} of actions){assert(B.contains(pull(r,M)),"invariance");ledger.linearSquares++}
 return {rows:agenda,ops,rank:agenda.length,code:x=>agenda.map(r=>Number(dot(r,x))).join("")};
}
let affine=[];for(let k=0;k<70;k++){let n=1+rnd(6),N=2**n,A=1+rnd(3),actions=seq(A).map(()=>({M:seq(n).map(()=>BigInt(rnd(N))),b:BigInt(rnd(N))})),O=seq(1+rnd(n)).map(()=>BigInt(rnd(N))),L=linearClosure(n,actions,O);
 let G={obs:seq(N).map(s=>O.map(r=>Number(dot(r,BigInt(s))))),edges:seq(N).map(s=>actions.map(({M,b})=>[Number(apply(M,BigInt(s),b)),1]))},Q=quotient(G);
 for(let s=0;s<N;s++)for(let t=s;t<N;t++){assert((L.code(BigInt(s))===L.code(BigInt(t)))===(Q.q[s]===Q.q[t]),"affine quotient mismatch");ledger.linearPairs++}
 affine.push({n,rank:L.rank,classes:Q.classes,rowPulls:L.ops});
}
let shifts=[];for(let n of [8,16,32,64,128,256]){let M=seq(n).map(i=>1n<<BigInt((i+1)%n)),L=linearClosure(n,[{M,b:0n}],[1n]);assert(L.rank===n,"delayed hidden bits");shifts.push({n,rank:L.rank,rowPulls:L.ops,explicitStates:"2^"+n})}
// Nonlinear exact residual identity on an integer trajectory, not a PDE.
// e_{j+1} = d_j + [B_a(Qs_j)-B_a(z_j)], using actual and reference.
const f=[x=>[x[0]+x[1],x[1]-1],x=>[x[0]-x[1],x[1]+2]],Q=x=>x[0];
for(let k=0;k<60;k++){let s=[rnd(9)-4,rnd(9)-4],z=BigInt(Q(s));let e=0n;for(let j=0;j<5;j++){let a=rnd(2),next=f[a](s),b=a===0?v=>v*v-2n:v=>2n*v+1n;
 let d=BigInt(Q(next))-b(BigInt(Q(s))),prop=b(BigInt(Q(s)))-b(z),newz=b(z),newE=BigInt(Q(next))-newz;
 assert(newE===d+prop&&e===BigInt(Q(s))-z,"signed nonlinear defect");ledger.defectChecks++;s=next;z=newz;e=newE}
}
// Original PNP cutset creation-order wire ABI (i/g, const/not/and/or).
// Compile all original input assignments into a finite pc-labelled trace.
// Costs are one unit per original gate event, not physical bit clocks.
function dagTrace(n,gates,out){
 const N=2**n,L=gates.length,read=(x,v,w)=>w[0]==="i"?((x>>w[1])&1):v[w[1]];
 const rows=seq(N).map(x=>{let v=[];for(let [op,args] of gates){let a=op==="const"?[]:args.map(w=>read(x,v,w));v.push(op==="const"?+args[0]:op==="not"?1-a[0]:op==="and"?a[0]&a[1]:a[0]|a[1])}return v});
 const ix=(pc,x)=>pc*N+x,G={obs:[],edges:[]};for(let pc=0;pc<=L;pc++)for(let x=0;x<N;x++){G.obs.push(pc===L?["halt",read(x,rows[x],out)]:["running",pc]);G.edges.push([pc===L?null:[ix(pc+1,x),1]])}
 let R=quotient(G),cutRows=[];for(let pc=0;pc<=L;pc++){let live=new Map();for(let w of [out,...gates.slice(pc).flatMap(([o,a])=>o==="const"?[]:a)])if(w[0]==="i"||w[1]<pc)live.set(key(w),w);
 let liveKeys=new Map();for(let x=0;x<N;x++){let k=key([...live.values()].map(w=>read(x,rows[x],w))),c=R.q[ix(pc,x)];assert(!liveKeys.has(k)||liveKeys.get(k)===c,"actual cut must factor future");liveKeys.set(k,c);ledger.dagChecks++}
 cutRows.push({pc,liveWires:live.size,liveValues:liveKeys.size,minFutureClasses:new Set(seq(N).map(x=>R.q[ix(pc,x)])).size});
 }return {n,gates:L,originalEvents:N*L,...verify(G,true,false),cutRows};
}
let dag=[];for(let n=2;n<=6;n++){let gates=[["not",[["i",0]]]];for(let i=1;i<n;i++)gates.push([i%2?"and":"or",[["g",i-1],["i",i]]]);dag.push(dagTrace(n,gates,["g",gates.length-1]))}
// NS rate radical: equal-rate pair sums annihilate (1,-1), but a
// deliberately distinct hypothetical evolution turns it into visible flux.
// This is a rational algebra control, not an actual Galerkin flow.
const rad={rates:[13,13,17],delta:[1,-1,0],test:[1,2,3]};
function num(a,b){let D=26*30*34;let z=0;for(let i=0;i<3;i++)for(let j=0;j<3;j++)z+=a[i]*b[j]*(D/(rad.rates[i]+rad.rates[j]));return z}
assert(num(rad.delta,rad.test)===0,"static radical");
let evolved=[1,-2,0];assert(num(evolved,rad.test)!==0,"dynamic leakage");rad.commonDenominator=26*30*34;rad.staticNumerator=0;rad.evolvedNumerator=num(evolved,rad.test);
return {status:"PASS",seed:4601,ledger,randomGraphs:random.length,counters,affineCases:affine.length,shifts,dag,rad,scope:"explicit finite graphs and symbolic affine algebra; not actual PDE, unrestricted TM or Clay proof"};
}
console.log(JSON.stringify(campaign(),null,2));
