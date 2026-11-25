import fs from 'node:fs';
function audit(book,source){
 const R=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3,d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],num=a=>a[0]+3*a[1]+9*a[2];
 const add=(a,b)=>num(d(a).map((x,i)=>mod(x+d(b)[i]))),sub=(a,b)=>num(d(a).map((x,i)=>mod(x-d(b)[i])));
 const mul=(a,b)=>{const x=d(a),y=d(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return num(z.slice(0,3).map(mod))};
 const A=R(27).map(a=>R(27).map(b=>add(a,b))),D=R(27).map(a=>R(27).map(b=>sub(a,b))),M=R(27).map(a=>R(27).map(b=>mul(a,b))),I=R(27).map(x=>x?M[x].indexOf(1):0);
 const gem=Array(27),gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"];for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i/9);v=Math.floor((i%9)/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
 const ix=new Map(gem.map((x,i)=>[x,i])),enc=s=>[...s].map(c=>{if(!ix.has(c))throw Error("glyph");return ix.get(c)}),all=R(27);
 const blocks=(lo,hi)=>book.chapters.filter(c=>c.c>=lo&&c.c<=hi).flatMap(c=>{const s=enc(c.verses.map(v=>v.letters).join(""));return R(Math.floor(s.length/216)).map(i=>({c:c.c,b:i,rows:[s.slice(i*216,i*216+72),s.slice(i*216+72,i*216+144).reverse(),s.slice(i*216+144,i*216+216)]}))});
 const target={c:14,b:0,rows:[enc(source.sourceRows[0]),enc(source.sourceRows[1]).reverse(),enc(source.sourceRows[2])]};
 const train=blocks(1,13),test=blocks(16,40);
 function frames(visible){const [a,b]=visible;return R(72).map(j=>{const pool=[b[j],a[j-1],b[j-1],a[j+1],b[j+1],a[j-2],b[j-2],a[j+2],b[j+2]],k=pool.findIndex(x=>x!==undefined&&x!==a[j]);if(k<0)return null;return {a:a[j],u:D[pool[k]][a[j]],k}})}
 const z=(f,x)=>M[I[f.u]][D[x][f.a]],restore=(f,r)=>A[f.a][M[f.u][r]];
 function edges(visible,kind){const fs=frames(visible);if(fs.some(f=>!f))return null;
  return {fs,trans:R(71).map(i=>{const f=fs[i],g=fs[i+1],delta=z(g,f.a);return all.map(r=>{let m=kind==="transport"?r:A[r][delta];return [...new Set([m,I[m]])]})})}
 }
 // Distinct glyph paths, not gate traces: coincident branches deduplicate.
 // Anchors independently supplied as observed glyphs only in the explicitly two-boundary mask.
 function solve(visible,kind,boundaries={}){
  const e=edges(visible,kind);if(!e)return null;const {fs,trans}=e,domains=R(72).map(j=>boundaries[j]===undefined?all:[z(fs[j],boundaries[j])]);
  const f=R(72).map(()=>Array(27).fill(0n)),b=R(72).map(()=>Array(27).fill(0n));
  for(const r of domains[0])f[0][r]=1n;
  for(let j=1;j<72;j++)for(const r of all)for(const t of trans[j-1][r])if(domains[j].includes(t))f[j][t]+=f[j-1][r];
  for(const r of domains[71])b[71][r]=1n;
  for(let j=70;j>=0;j--)for(const r of domains[j])for(const t of trans[j][r])b[j][r]+=b[j+1][t];
  const count=f[71].reduce((a,x)=>a+x,0n),back=domains[0].reduce((a,x)=>a+b[0][x],0n);if(count!==back)throw Error("bidi count");
  const supports=R(72).map(j=>all.filter(r=>f[j][r]&&b[j][r]).map(r=>restore(fs[j],r)));
  if(count>0n)for(let j=0;j<72;j++){const mass=all.reduce((a,r)=>a+f[j][r]*b[j][r],0n);if(mass!==count)throw Error("separator mass")}
  return {fs,trans,count,supports}
 }
 function score(block,kind,knownEnds=false){
  const visible=block.rows.slice(0,2),truth=block.rows[2],bound=knownEnds?{0:truth[0],71:truth[71]}:{},s=solve(visible,kind,bound);if(!s)return {missingFrame:true};
  const rr=truth.map((x,j)=>z(s.fs[j],x)),bad=R(71).filter(i=>!s.trans[i][rr[i]].includes(rr[i+1])),idx=knownEnds?R(70).map(i=>i+1):R(72);
  return {paths:s.count.toString(),bits:s.count?Math.log2(Number(s.count)):null,badEdges:bad.length,firstBad:bad[0]??null,truthPath:!bad.length,zeroPaths:s.count===0n,singleton:idx.filter(j=>s.supports[j].length===1).length,correctSingleton:idx.filter(j=>s.supports[j].length===1&&s.supports[j][0]===truth[j]).length,truthSupport:idx.filter(j=>s.supports[j].includes(truth[j])).length,output:idx.map(j=>s.supports[j].length===1?gem[s.supports[j][0]]:"?").join(""),supportSizes:idx.map(j=>s.supports[j].length)}
 }
 function summary(bs,kind,knownEnds){let n=0,missingFrames=0,badEdges=0,truePaths=0,zeroPaths=0,uniquePaths=0,singleton=0,correctSingleton=0,truthSupport=0;for(const block of bs){const s=score(block,kind,knownEnds);if(s.missingFrame){missingFrames++;continue}n++;badEdges+=s.badEdges;truePaths+=s.truthPath;zeroPaths+=s.zeroPaths;uniquePaths+=s.paths==="1";singleton+=s.singleton;correctSingleton+=s.correctSingleton;truthSupport+=s.truthSupport}return {blocks:bs.length,solvedFrames:n,missingFrames,badEdges,truePaths,zeroPaths,uniquePaths,singleton,correctSingleton,truthSupport,withheld:bs.length*(knownEnds?70:72)}}
 // Reverse-solve exact minimum branch budget for a shared normalized state transition.
 // Current normalized residual is available to a causal generator only after it predicts the previous glyph.
 // For this oracle lower bound use true previous residual; never credit this as blind prediction.
 const keyers={state:(r,h)=>[r],stateAndPhase:(r,h)=>[r,h.j%4],stateAndDrift:(r,h)=>[r,h.delta],stateDriftPhase:(r,h)=>[r,h.delta,h.j%4],stateDriftGateFrame:(r,h)=>[r,h.delta,h.k,h.l]};
 function branchBudget(bs,key){const m=new Map();for(const block of bs){const fs=frames(block.rows.slice(0,2));if(fs.some(f=>!f))continue;const r=block.rows[2].map((x,j)=>z(fs[j],x));for(let j=1;j<72;j++){const k=key(r[j-1],{j,delta:z(fs[j],fs[j-1].a),k:fs[j-1].k,l:fs[j].k}).join();if(!m.has(k))m.set(k,Array(27).fill(0));m.get(k)[r[j]]++}}
  let max=0,bad=0,oracle2=0,n=0;let histogram={};for(const c of m.values()){const s=c.filter(x=>x>0).length;max=Math.max(max,s);bad+=s>2;histogram[s]=(histogram[s]||0)+1;const a=c.slice().sort((x,y)=>y-x);oracle2+=a[0]+a[1];n+=c.reduce((x,y)=>x+y,0)}return {keys:m.size,maxDistinctNext:max,keysExceedTwo:bad,oracleTwoBranchCoverage:oracle2,edges:n,histogram}
 }
 const variants={};for(const kind of ["transport","drift"]){variants[kind]={shemFree:score(target,kind),shemEnds:score(target,kind,true),trainFree:summary(train,kind,false),testFree:summary(test,kind,false),testEnds:summary(test,kind,true)}}
 return {variants,branchBudget:Object.fromEntries(Object.entries(keyers).map(([k,v])=>[k,branchBudget(train,v)])),qualification:"Constructed M/F candidates, not creator law: M preserves normalized residual (transport) or adds visible interframe drift; F applies zero-extended inversion to M. All third-row glyphs withheld in free mask; endpoints explicitly observed in separate 70-hole mask. Exact path counts and supports, no linguistic fallback. Actual source and reused synthetic chapter blocks are regression data, not fresh blind holdout. Gate budget is training oracle with true previous state, not achieved prediction."}
}
const base='Docs/support/reference/TorahCryptoCorpus20261125/';
console.log(JSON.stringify(audit(...['exodus.normalized.json','h20-source-role-residual.json'].map(n=>JSON.parse(fs.readFileSync(base+n,'utf8')))),null,2));
