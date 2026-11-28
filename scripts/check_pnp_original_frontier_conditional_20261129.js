// Section 49 original exact-cover frontier conditional counts. Node.js.
function campaign(){
"use strict";
const assert=(x,m)=>{if(!x)throw Error(m)},range=n=>Array.from({length:n},(_,i)=>i),bit=i=>1n<<BigInt(i);
const original=[[2,10,15],[7,9,12],[3,4,14],[0,6,16],[1,5,13],[8,11,17],[9,15,16],[0,8,14],[2,6,17],[5,10,13],[1,3,12],[4,7,11],[3,11,12],[1,2,6],[0,7,14],[4,9,15],[10,13,17],[5,8,16],[0,1,14],[4,9,16],[7,12,15],[2,5,17],[3,6,11],[8,10,13],[0,1,9],[4,11,17],[3,6,16],[2,10,12],[5,14,15],[7,8,13]];
const pop=x=>{let c=0;while(x){x&=x-1n;c++}return c};
function solve(cols,r,order,limits){
 const n=cols.length,all=bit(r)-1n;assert(order.length===n&&new Set(order).size===n&&order.every(i=>Number.isInteger(i)&&i>=0&&i<n),"order");assert(cols.every(c=>c>=0n&&(c&~all)===0n),"rows");
 const C=order.map(i=>cols[i]),suffix=Array(n+1).fill(0n),prefix=Array(n+1).fill(0n);
 for(let i=n-1;i>=0;i--)suffix[i]=suffix[i+1]|C[i];
 for(let i=0;i<n;i++)prefix[i+1]=prefix[i]|C[i];
 const frontier=prefix.map((p,i)=>p&suffix[i]),width=Math.max(...frontier.map(pop));
 let stats={width,states:0,edges:0,peakLayer:0};if(suffix[0]!==all)return {status:"EXACT",total:0n,counts:null,stats};
 if(width>limits.width)return {status:"CENSORED",reason:"width",stats};
 const memo=range(n+1).map(()=>new Map());let refused=false;
 function transitions(i,m){let a=[];for(let b=0;b<2;b++){if(b&&(m&C[i]))continue;let z=m|(b?C[i]:0n);let retiring=suffix[i]&~suffix[i+1];if((z&retiring)!==retiring)continue;a.push([b,z&frontier[i+1]])}return a}
 function back(i,m){if(refused)return 0n;if(i===n)return 1n;if(memo[i].has(m))return memo[i].get(m);
 if(stats.states>=limits.states){refused=true;return 0n}stats.states++;let v=0n;for(let [b,z] of transitions(i,m)){stats.edges++;v+=back(i+1,z)}memo[i].set(m,v);stats.peakLayer=Math.max(stats.peakLayer,memo[i].size);return v}
 const total=back(0,0n);if(refused)return {status:"CENSORED",reason:"states",stats};
 let F=new Map([[0n,1n]]),counts=range(n).map(()=>[0n,0n]),witness=0n,m=0n;
 for(let i=0;i<n;i++){let next=new Map();for(let [s,a] of F)for(let [b,z] of transitions(i,s)){let q=back(i+1,z);counts[order[i]][b]+=a*q;if(q)next.set(z,(next.get(z)||0n)+a)}F=next;
 if(total){let e=transitions(i,m).find(([b,z])=>back(i+1,z)>0n);assert(e,"reopen");if(e[0])witness|=bit(order[i]);m=e[1]}}
 assert(counts.every(c=>c[0]+c[1]===total),"conditional sum");
 return {status:"EXACT",total,counts,witness,stats,order};
}
function valid(cols,r,w){let s=0n;for(let i=0;i<cols.length;i++)if(w&bit(i)){if(s&cols[i])return false;s|=cols[i]}return s===bit(r)-1n}
function greedy(cols){let remaining=new Set(range(cols.length)),p=0n,o=[];while(remaining.size){let best=-1,score=Infinity;for(let i of remaining){let future=0n;for(let j of remaining)if(i!==j)future|=cols[j];let x=pop((p|cols[i])&future);if(x<score){best=i;score=x}}remaining.delete(best);o.push(best);p|=cols[best]}return o}
let seed=4901;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};let checks=0,random=0;
for(let t=0;t<120;t++){let n=1+rnd(11),r=1+rnd(8),cols=range(n).map(()=>BigInt(rnd(2**r))),Q=solve(cols,r,greedy(cols),{width:20,states:100000});assert(Q.status==="EXACT","random");let total=0n,C=range(n).map(()=>[0n,0n]);for(let w=0;w<2**n;w++)if(valid(cols,r,BigInt(w))){total++;for(let i=0;i<n;i++)C[i][(w>>i)&1]++}assert(Q.total===total,"count");if(Q.counts){for(let i=0;i<n;i++){assert(Q.counts[i].every((c,b)=>c===C[i][b]),"condition");checks+=2}}if(total)assert(valid(cols,r,Q.witness),"witness");random++}
const cols=original.map(s=>s.reduce((a,i)=>a|bit(i),0n)),order=greedy(cols),Q=solve(cols,18,order,{width:18,states:1000000});assert(Q.total===7n&&valid(cols,18,Q.witness),"original fixture");
let independent=[];function exactCover(covered,w){if(covered===bit(18)-1n){independent.push(w);return}let j=0;while(covered&bit(j))j++;for(let i=0;i<cols.length;i++)if((cols[i]&bit(j))&&!(cols[i]&covered))exactCover(covered|cols[i],w|bit(i))}
exactCover(0n,0n);assert(independent.length===7&&new Set(independent).size===7,"independent exact cover");
for(let i=0;i<30;i++)for(let b=0;b<2;b++){assert(Q.counts[i][b]===BigInt(independent.filter(w=>Number((w>>BigInt(i))&1n)===b).length),"original conditional");checks++}
let refuse=solve(cols,18,order,{width:0,states:100});assert(refuse.status==="CENSORED","width refusal");let cap=solve(cols,18,order,{width:18,states:1});assert(cap.status==="CENSORED","state refusal");
return {status:"PASS",random,checks,original:{count:Q.total.toString(),counts:Q.counts.map(c=>c.map(String)),witness:Q.witness.toString(),stats:Q.stats,order,independent:independent.map(String)},refusals:[refuse.reason,cap.reason]};
}
console.log(JSON.stringify(campaign(),null,2));
