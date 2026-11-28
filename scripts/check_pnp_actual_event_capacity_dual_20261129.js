// Section50 finite same-run event attachment primal/dual referee.
function campaign(){
"use strict";
const assert=(x,m)=>{if(!x)throw Error(m)},seq=n=>Array.from({length:n},(_,i)=>i);
function allocate(dem,cap,adj){
 const m=dem.length,n=cap.length,S=m+n,T=S+1,N=T+1,total=dem.reduce((a,b)=>a+b,0);
 assert([...dem,...cap].every(x=>Number.isSafeInteger(x)&&x>=0)&&Number.isSafeInteger(total+1),"invalid capacity");
 const G=seq(N).map(()=>[]);
 function edge(a,b,c){let f={to:b,rev:G[b].length,c,orig:c},r={to:a,rev:G[a].length,c:0,orig:0};G[a].push(f);G[b].push(r);return f}
 const src=dem.map((d,i)=>edge(S,i,d)),dst=cap.map((c,j)=>edge(m+j,T,c)),arc=adj.map((js,i)=>[...new Set(js)].map(j=>{assert(Number.isInteger(j)&&j>=0&&j<n,"event");return [j,edge(i,m+j,total+1)]}));
 let flow=0,augmentations=0,scans=0;
 while(true){let prev=Array(N).fill(null),q=[S];prev[S]=[-1,-1];for(let i=0;i<q.length&&prev[T]===null;i++){let v=q[i];for(let k=0;k<G[v].length;k++){let e=G[v][k];scans++;if(e.c>0&&prev[e.to]===null){prev[e.to]=[v,k];q.push(e.to)}}}
 if(prev[T]===null)break;
 let a=Infinity;for(let v=T;v!==S;){let [u,k]=prev[v];a=Math.min(a,G[u][k].c);v=u}
 for(let v=T;v!==S;){let [u,k]=prev[v],e=G[u][k];e.c-=a;G[v][e.rev].c+=a;v=u}
 flow+=a;augmentations++;
 }
 let seen=new Set([S]),q=[S];for(let i=0;i<q.length;i++)for(let e of G[q[i]])if(e.c>0&&!seen.has(e.to)){seen.add(e.to);q.push(e.to)}
 let U=seq(m).filter(i=>seen.has(i)),V=[...new Set(U.flatMap(i=>adj[i]))].sort((a,b)=>a-b);
 const deficit=U.reduce((a,i)=>a+dem[i],0)-V.reduce((a,j)=>a+cap[j],0);
 const rows=arc.map(es=>es.map(([j,e])=>[j,e.orig-e.c]).filter(x=>x[1]!==0)),col=seq(n).map(()=>0);
 let value=0;for(let i=0;i<m;i++){let r=0;for(let [j,c] of rows[i]){assert(adj[i].includes(j)&&c>=0,"primal edge");r+=c;col[j]+=c}assert(r<=dem[i]&&r===src[i].orig-src[i].c,"primal demand");value+=r}
 assert(col.every((v,j)=>v<=cap[j]&&v===dst[j].orig-dst[j].c),"event capacity");assert(value===flow&&deficit===total-flow,"primal/dual equality");
 return {status:flow===total?"PACKED":"DEFICIENT",flow,deficit,obligations:U,events:V,rows,augmentations,scans};
}
let seed=5002;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
let counts={networks:0,subsetDuals:0,epochs:0,runs:0,alternatives:0,retained:0,packed:0,deficient:0,eventChecks:0};
for(let k=0;k<256;k++){let m=rnd(8),n=rnd(7),dem=seq(m).map(()=>rnd(4)),cap=seq(n).map(()=>rnd(4)),adj=seq(m).map(()=>seq(n).filter(()=>rnd(2))),r=allocate(dem,cap,adj),max=0;
 for(let x=0;x<1<<m;x++){let U=seq(m).filter(i=>x>>i&1),V=new Set(U.flatMap(i=>adj[i]));max=Math.max(max,U.reduce((a,i)=>a+dem[i],0)-[...V].reduce((a,j)=>a+cap[j],0));counts.subsetDuals++}assert(r.deficit===max,"independent Hall dual");counts.networks++}
function run(g,x,k,s){let states=[s],reads=[];for(let i=0;i<k;i++){let [j,a,b]=g[s];reads.push(j);s=x>>j&1?b:a;states.push(s)}return {states,reads,end:s}}
let totals={demand:0,actualEvents:0,packedUnits:0,deficit:0};
for(let k=0;k<64;k++){let n=2+rnd(5),m=2+rnd(8),g=seq(m).map(()=>[rnd(n),rnd(m),rnd(m)]),N=1<<n,p=seq(N).map(()=>0),epochStart=0;
 for(let length of [1,2,3,5]){let A=seq(N).map(x=>run(g,x,length,p[x]));for(let x=0;x<N;x++){
 let r=A[x],D=[];for(let y=0;y<N;y++){if(p[x]!==p[y]||r.end===A[y].end)continue;let e=[];for(let i=0;i<length;i++)if(r.states[i]===A[y].states[i]&&r.states[i+1]!==A[y].states[i+1]){let j=r.reads[i];assert(j===A[y].reads[i]&&((x^y)>>j&1),"actual divergence");e.push(i);counts.eventChecks++}
 assert(e.length,"first divergence");D.push({support:x^y,events:e,y});counts.alternatives++}
 D.sort((a,b)=>a.support.toString(2).replace(/0/g,"").length-b.support.toString(2).replace(/0/g,"").length||a.support-b.support);let K=[];
 for(let d of D)if(!K.some(z=>(z.support&d.support)===z.support))K.push(d);
 // Each retained support is a CANDIDATE unit demand, not an independently
 // established nonamortizable obligation. Test simultaneous feasibility.
 let f=allocate(K.map(()=>1),seq(length).map(()=>1),K.map(d=>d.events));
 for(let i=0;i<K.length;i++)for(let [j,a] of f.rows[i])assert(K[i].events.includes(j)&&epochStart+j>=epochStart&&a===1,"event ID");
 assert(f.flow<=length,"same-run");counts.runs++;counts.retained+=K.length;counts[f.status==="PACKED"?"packed":"deficient"]++;
 totals.demand+=K.length;totals.actualEvents+=length;totals.packedUnits+=f.flow;totals.deficit+=f.deficit;
 }p=A.map(r=>r.end);epochStart+=length;counts.epochs++}
}
// Multiple incomparable original disagreement supports can attach to one
// actual observation event only if the source schedule reads a common bit.
// Distinct unit demands are NOT justified merely by this construction.
// Literal adaptive AND-OR program. At all-zero x the output is false;
// each minimal different-output support is {0,i}. They all separate
// at the SAME first observation, even though there are 4 alternatives.
// A padded sink performs no useful new distinction.
const n=5,g=[[0,1,3],[0,1,1],[0,2,2],...seq(n-1).map((_,j)=>[j+1,j===n-2?1:j+4,2])];
const baseline=run(g,0,n,0),alts=[];
assert(baseline.end===1,"baseline false");
for(let y=0;y<1<<n;y++)if(run(g,y,n,0).end===2)alts.push(y);
const minimal=alts.filter(y=>!alts.some(z=>z!==y&&(z&y)===z));
assert(minimal.length===4&&minimal.every(y=>(y&1)&&((y-1)&(y-2))===0),"actual minimal alternatives");
const eligible=minimal.map(y=>{let q=run(g,y,n,0);return seq(n).filter(i=>baseline.states[i]===q.states[i]&&baseline.states[i+1]!==q.states[i+1])});
assert(eligible.every(e=>e.length===1&&e[0]===0),"actual shared divergence");
const actualOverlap=allocate(minimal.map(()=>1),seq(n).map(()=>1),eligible);
assert(actualOverlap.flow===1&&actualOverlap.deficit===3,"actual candidate overcharge");
let overlap=allocate([1,1,1,1],[1],[[0],[0],[0],[0]]);
assert(overlap.deficit===3&&overlap.flow===1,"shared event rejection");
let disjoint=allocate([1,1,1],[1,1,1],[[0],[1],[2]]);assert(disjoint.flow===3,"disjoint packing");
return {status:"PASS",counts,totals,overlap:{flow:overlap.flow,deficit:overlap.deficit},actualOverlap:{minimal,eligible,flow:actualOverlap.flow,deficit:actualOverlap.deficit},scope:"finite actual adaptive read epochs; candidate attachment feasibility, not unavoidable demands or arbitrary machine lower bounds"};
}
console.log(JSON.stringify(campaign(),null,2));
