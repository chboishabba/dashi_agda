import fs from 'node:fs';
function assay(book){
 const alphabet=[..."אבגדהוזחטיךכלםמןנסעףפץצקרשת"], K=alphabet.length, ix=new Map(alphabet.map((c,i)=>[c,i]));
 if(K!==27||ix.size!==27)throw Error("alphabet");
 const rows=book.chapters.map(c=>({c:c.c,seq:[...c.verses.map(v=>v.letters).join("")].map(x=>{if(!ix.has(x))throw Error("glyph");return ix.get(x)})}));
 const range=n=>Array.from({length:n},(_,i)=>i),vec=()=>range(K).map(()=>0),mat=()=>range(K).map(vec),blocks=seq=>range(Math.floor(seq.length/216)).map(i=>seq.slice(i*216,(i+1)*216));
 const enc=i=>[Math.floor(i/72),Math.floor(i%72/9),Math.floor(i%9/3)-1,i%3-1],dec=([r,q,a,b])=>72*r+9*q+3*(a+1)+b+1;
 const act=([r,q,a,b],g)=>g===0&&r!==1?[r,q,a,b]:g===2?[r,q^4,a,b]:[g===1?2-r:r,7-q,-a,-b];
 const perm=range(8).map(m=>range(216).map(i=>dec(range(3).reduce((x,g)=>m&(1<<g)?act(x,g):x,enc(i)))));
 const train=rows.filter(r=>r.c<=13),test=rows.filter(r=>r.c>=16),trainBlocks=train.flatMap(r=>blocks(r.seq)),testBlocks=test.flatMap(r=>blocks(r.seq));
 const uni=vec(),positions=range(216).map(vec),pairs=range(8).map(mat),trans=mat();
 for(const r of train){for(let i=0;i<r.seq.length;i++){uni[r.seq[i]]++;if(i)trans[r.seq[i-1]][r.seq[i]]++}}
 for(const b of trainBlocks)for(let j=0;j<216;j++){positions[j][b[j]]++;for(let m=1;m<8;m++)if(perm[m][j]!==j)pairs[m][b[perm[m][j]]][b[j]]++}
 const normalize=a=>{let s=a.reduce((x,y)=>x+y,0);return a.map(x=>x/s)};
 const prior=normalize(uni.map(x=>x+1)),pos=positions.map(a=>normalize(a.map((n,i)=>n+10*prior[i]))),transition=trans.map(a=>normalize(a.map((n,i)=>n+10*prior[i]))),conditional=pairs.map(m=>m.map(a=>normalize(a.map((n,i)=>n+10*prior[i]))));
 const argmax=a=>a.reduce((b,x,i)=>x>a[b]?i:b,0);
 const names=["uniform","unigram","position216","geometry","markovMarginal","hybrid"];
 function predict(prefix){
  let marginal=vec();marginal[prefix.at(-1)]=1;
  const pred=Object.fromEntries(names.map(n=>[n,[]]));
  for(let j=125;j<216;j++){
   const peers=new Map();
   for(let m=1;m<8;m++){const k=perm[m][j];if(k<prefix.length&&!peers.has(k))peers.set(k,conditional[m][prefix[k]])}
   const distributions=[pos[j],...peers.values()];
   const geom=range(K).map(i=>distributions.reduce((s,a)=>s+a[i],0)/distributions.length);
   marginal=range(K).map(i=>marginal.reduce((s,p,k)=>s+p*transition[k][i],0));
   const ps=[range(K).map(()=>1/K),prior,pos[j],geom,marginal,range(K).map(i=>(geom[i]+marginal[i])/2)];
   for(let k=0;k<names.length;k++)pred[names[k]].push({p:ps[k],symbol:argmax(ps[k]),peers:peers.size});
  }return pred;
 }
 const metrics=Object.fromEntries(names.map(n=>[n,{n:0,hits:0,bits:0,top3:0}]));
 for(const b of testBlocks){const pred=predict(b.slice(0,125));for(const n of names)for(let j=0;j<91;j++){const t=b[125+j],x=pred[n][j],s=metrics[n];s.n++;s.hits+=x.symbol===t;s.bits-=Math.log2(x.p[t]);s.top3+=x.p.map((v,i)=>[v,i]).sort((a,b)=>b[0]-a[0]||a[1]-b[1]).slice(0,3).some(z=>z[1]===t)}}
 for(const s of Object.values(metrics)){s.accuracy=s.hits/s.n;s.bitsPerLetter=s.bits/s.n;s.top3Rate=s.top3/s.n}
 const actual=rows.find(r=>r.c===14).seq.slice(8*216),continuation=rows.find(r=>r.c===15).seq.slice(0,91);if(actual.length!==125)throw Error("target");
 const target=predict(actual),candidates=Object.fromEntries(names.map(n=>[n,{text:target[n].map(x=>alphabet[x.symbol]).join(""),meanConfidence:target[n].reduce((s,x)=>s+x.p[x.symbol],0)/91,continuationHits:target[n].filter((x,i)=>x.symbol===continuation[i]).length,continuationBits:target[n].reduce((s,x,i)=>s-Math.log2(x.p[continuation[i]]),0)/91}]));
 const coverage=target.geometry.filter(x=>x.peers>0).length;
 // Explicit hard erasure hypotheses: repeated symbol or additive F3^3 parity zero on each orbit. Alphabet ordinal chart is artificial and frozen, not source semantics.
 const orbitMap=new Map();for(let i=0;i<216;i++){const o=[...new Set(perm.map(m=>m[i]))].sort((a,b)=>a-b);orbitMap.set(o.join(","),o)}
 const orbits=[...orbitMap.values()],digits=i=>[i%3,Math.floor(i/3)%3,Math.floor(i/9)],sum=v=>v.reduce((a,i)=>a.map((x,k)=>(x+digits(i)[k])%3),[0,0,0]);
 function parityStats(bs){let n=0,zero=0,constant=0;for(const b of bs)for(const o of orbits){if(o.length<2)continue;n++;const v=o.map(j=>b[j]);zero+=sum(v).every(x=>x===0);constant+=v.every(x=>x===v[0])}return {n,zero,constant}}
 const targetOrbits=orbits.map(o=>({positions:o,observed:o.filter(i=>i<125),missing:o.filter(i=>i>=125)}));
 const singles=targetOrbits.filter(o=>o.missing.length===1),parityCandidates=singles.map(o=>{const d=sum(o.observed.map(i=>actual[i])).map(x=>(3-x)%3);return {position:o.missing[0],glyph:alphabet[d[0]+3*d[1]+9*d[2]]}});
 const unresolvedDimension=targetOrbits.reduce((s,o)=>s+Math.max(0,o.missing.length-1),0);

 function constrained(prefix){
   const p=predict(prefix).geometry;
   const filled=prefix.concat(range(91).map(()=>-1));
   for(const o of orbits){
     const missing=o.filter(j=>j>=125);
     const known=sum(o.filter(j=>j<125).map(j=>prefix[j]));
     if(!missing.length){if(known.some(x=>x!==0))return null;continue}
     if(missing.length>2)throw Error("unexpected shape");
     let best=-Infinity,bestVals=null;
     for(const i of range(missing.length===2?K:1)){
       const d=missing.length===2?digits(i):[0,0,0];
       const z=known.map((v,k)=>(6-v-d[k])%3),last=z[0]+3*z[1]+9*z[2];
       const vals=missing.length===2?[i,last]:[last];
       const score=vals.reduce((s,x,k)=>s+Math.log2(p[missing[k]-125].p[x]),0);
       if(score>best){best=score;bestVals=vals}
     }
     for(let k=0;k<missing.length;k++)filled[missing[k]]=bestVals[k];
   }
   if(orbits.some(o=>sum(o.map(j=>filled[j])).some(x=>x!==0)))throw Error("parity");
   return filled.slice(125);
 }
 const completed=constrained(actual);
 let parityHits=0,validBlocks=0,allCorrect=0;
 for(const b of testBlocks){
    const z=constrained(b.slice(0,125));
    if(z){validBlocks++;const hits=z.filter((x,i)=>x===b[125+i]).length;parityHits+=hits;allCorrect+=hits===91}
 }
 const completion={text:completed.map(i=>alphabet[i]).join(""),allOrbitEquationsSatisfied:true,continuationHits:completed.filter((x,i)=>x===continuation[i]).length,testValidBlocks:validBlocks,testHits:parityHits,testLetters:91*validBlocks,testAccuracy:parityHits/(91*validBlocks),exactHeldoutSuffixes:allCorrect,qualifier:"MAP under invented parity constraints; not original text. No fully observed target orbits, so observed-prefix parity is vacuous. Most true heldout orbit sums are nonzero."};

 return {completion,alphabet:alphabet.join(""),trainChapters:[1,13],testChapters:[16,40],trainBlocks:trainBlocks.length,testBlocks:testBlocks.length,metrics,coverage,uncovered:91-coverage,candidates,actualContinuation:continuation.map(i=>alphabet[i]).join(""),parity:{orbits:orbits.length,orbitSizes:Object.fromEntries([1,2,4,8].map(n=>[n,orbits.filter(o=>o.length===n).length])),train:parityStats(trainBlocks),test:parityStats(testBlocks),targetMissingOrbits:targetOrbits.filter(o=>o.missing.length).length,singleMissing:singles.length,parityCandidates,unresolvedDimension,conditionalFreeTrits:3*unresolvedDimension,fullyObservedViolations:targetOrbits.filter(o=>!o.missing.length&&!sum(o.observed.map(i=>actual[i])).every(x=>x===0)).length},qualification:"Chosen ordinal alphabet map and candidate cipher assumptions; no evidence of source intent. Held-out blocks are disjoint chapters but within same book; continuation comparison not a test of a missing manuscript entry."};
}
const book=JSON.parse(fs.readFileSync(process.argv[2] || 'Docs/support/reference/TorahCryptoCorpus20261125/exodus.normalized.json','utf8'));
console.log(JSON.stringify(assay(book),null,2));
