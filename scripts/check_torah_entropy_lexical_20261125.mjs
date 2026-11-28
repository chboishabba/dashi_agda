import fs from 'node:fs';
function assay(book,words){
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


 const entropy=a=>{const c=vec();for(const i of a)c[i]++;return c.reduce((s,n)=>n?s-n/a.length*Math.log2(n/a.length):s,0)};
 const groups={det:[],free:[],slave:[]};
 for(const o of targetOrbits){const m=o.missing.map(i=>i-125);if(m.length===1)groups.det.push(m[0]);else{groups.free.push(m[0]);groups.slave.push(m[1])}}
 if(Object.values(groups).flat().length!==91||new Set(Object.values(groups).flat()).size!==91)throw Error("partition");
 let rng=0x15a369;const random=()=>{rng=(Math.imul(rng,1664525)+1013904223)>>>0;return (rng+.5)/4294967296};
 function sample(prefix,T){
  const p=predict(prefix).geometry,filled=prefix.concat(range(91).map(()=>-1));
  for(const o of targetOrbits){const m=o.missing,k=sum(o.observed.map(j=>prefix[j]));
   const opts=range(m.length===2?27:1).map(i=>{const d=m.length===2?digits(i):[0,0,0],z=k.map((x,j)=>(6-x-d[j])%3),last=z[0]+3*z[1]+9*z[2],v=m.length===2?[i,last]:[last];return {v,log:v.reduce((s,x,j)=>s+Math.log(p[m[j]-125].p[x]),0)}});
   let best=opts.reduce((a,b)=>a.log>=b.log?a:b);
   if(T>0&&opts.length>1){const w=opts.map(x=>T===Infinity?1:Math.exp((x.log-best.log)/T)),z=w.reduce((a,b)=>a+b,0);let u=random()*z;let i=0;while(i<w.length-1&&u>=w[i])u-=w[i++];best=opts[i]}
   m.forEach((j,i)=>filled[j]=best.v[i]);
  }
  if(orbits.some(o=>sum(o.map(j=>filled[j])).some(x=>x)))throw Error("sample parity");
  return filled.slice(125);
 }
 const groupStat=a=>({det:entropy(groups.det.map(i=>a[i])),free:entropy(groups.free.map(i=>a[i])),slave:entropy(groups.slave.map(i=>a[i])),all:entropy(a),gradient:entropy(a.slice(0,27))-entropy(a.slice(-27)),vowel:a.filter(i=>"אהוי".includes(alphabet[i])).length/a.length,tail:(()=>{let n=0;for(let j=a.length-1;j>=0&&"אהוי".includes(alphabet[a[j]]);j--)n++;return n})()});
 const modes=[0,1,2,4,Infinity],ablation=[];
 const maps=testBlocks.map(b=>constrained(b.slice(0,125)));
 for(const T of modes){
   const samples=T===0?maps:testBlocks.map(b=>sample(b.slice(0,125),T));
   const stat=samples.map(groupStat),target=T===0?completed:sample(actual,T);
   const means=Object.fromEntries(Object.keys(stat[0]).map(k=>[k,stat.reduce((s,x)=>s+x[k],0)/stat.length]));
   const hits=samples.reduce((s,a,k)=>s+a.filter((x,j)=>x===testBlocks[k][125+j]).length,0);
   ablation.push({temperature:T===Infinity?"uniform feasible":T,means,hits,letters:testBlocks.length*91,target:groupStat(target),targetText:target.map(i=>alphabet[i]).join(""),parityChecks:54*samples.length});
 }
 const real=testBlocks.map(b=>groupStat(b.slice(125))),realMeans=Object.fromEntries(Object.keys(real[0]).map(k=>[k,real.reduce((s,x)=>s+x[k],0)/real.length]));
 const a=completed.map(i=>alphabet[i]).join("");
 // Frozen training word tokens from the original written XML, not a full morphology lexicon.
 const counts=new Map();for(const w of words)counts.set(w,(counts.get(w)||0)+1);
 const maxLen=Math.max(...[...counts.keys()].map(w=>w.length));
 const literalCost=s=>[...s].reduce((v,c)=>v-Math.log2(prior[ix.get(c)]),0);
 // Known length, prefix-decodable ideal arithmetic mixture: 1 bit token class + conditional token cost. No separate space charge.
 function segment(s,allowLiteral){
  const dp=range(s.length+1).map(()=>Infinity),prev=range(s.length+1).map(()=>null);dp[0]=0;
  for(let i=0;i<s.length;i++)if(Number.isFinite(dp[i])){
   const offer=(j,kind,w,c)=>{if(dp[i]+c<dp[j]){dp[j]=dp[i]+c;prev[j]={i,kind,w,c}}};
   if(allowLiteral)offer(i+1,"literal",s[i],1-Math.log2(prior[ix.get(s[i])]));
   for(let j=i+1;j<=Math.min(s.length,i+maxLen);j++){const w=s.slice(i,j),n=counts.get(w);if(n)offer(j,"word",w,1-Math.log2(n/words.length))}
  }
  if(!Number.isFinite(dp[s.length]))return {possible:false};
  const path=[];for(let j=s.length;j;){const x=prev[j];path.push(x);j=x.i}path.reverse();
  if(path.map(x=>x.w).join("")!==s)throw Error("lexical inverse");
  return {possible:true,bits:dp[s.length],path,wordLetters:path.filter(x=>x.kind==="word").reduce((s,x)=>s+x.w.length,0),literalLetters:path.filter(x=>x.kind==="literal").length};
 }
 function lex(s){const mixed=segment(s,true),exact=segment(s,false);return {bits:mixed.bits,literalBits:literalCost(s),gain:literalCost(s)-mixed.bits,wordLetters:mixed.wordLetters,exact:exact.possible,exactBits:exact.bits??null}}
 const shuffle=s=>{const a=[...s];for(let i=a.length-1;i>0;i--){let j=Math.floor(random()*(i+1));[a[i],a[j]]=[a[j],a[i]]}return a.join("")};
 const lexTarget=lex(a),nulls=range(1000).map(()=>lex(shuffle(a))),mapLex=maps.map(x=>lex(x.map(i=>alphabet[i]).join(""))),realLex=testBlocks.map(b=>lex(b.slice(125).map(i=>alphabet[i]).join("")));
 const summary=x=>({n:x.length,meanGain:x.reduce((s,z)=>s+z.gain,0)/x.length,meanWordLetters:x.reduce((s,z)=>s+z.wordLetters,0)/x.length,exact:x.filter(z=>z.exact).length,atLeastTarget:x.filter(z=>z.gain>=lexTarget.gain).length});
 const literalChoice=segment(a,true);
 // Reversible explicit insertion ledger for proposed phrase. Original position is code-point index, no inferred meaning.
 const fragment="אתליום",reading="אתלייום",offset=a.indexOf(fragment),edit={kind:"insert",position:3,glyph:"י"};
 const repaired=fragment.slice(0,edit.position)+edit.glyph+fragment.slice(edit.position);
 if(repaired!==reading||repaired.slice(0,edit.position)+repaired.slice(edit.position+1)!==fragment||offset<0)throw Error("edit inverse");
 // fixed one-edit example: conditional on source length and one insertion; type 2 bits, position ceil(log2(n+1)), glyph ceil(log2(27)); general ledger must also code edit count.
 const editBits=2+Math.ceil(Math.log2(a.length+1))+Math.ceil(Math.log2(27));
 return {source:"33b275af62fa original decoder; same training/heldout splits",groups:Object.fromEntries(Object.entries(groups).map(([k,v])=>[k,v.map(i=>i+1).sort((a,b)=>a-b)])),ablation,realMeans,lexicon:{tokens:words.length,types:counts.size,maxLen,source:"pinned WLC Exodus chapters 1–13 w/k XML word slots; not morphology",target:lexTarget,exact:segment(a,false),mixed:literalChoice,nulls:summary(nulls),synthetic:summary(mapLex),originals:summary(realLex),continuation:lex(continuation.map(i=>alphabet[i]).join("")),editExample:{fragment,reading,offset,edit,conditionalBits:editBits}},notes:"Fixed temperature grid, one seeded draw per block per temperature; no temperature tuned on heldout. Entropy is empirical marginal, not entropy rate. Lexical cost ideal code conditional on shared train model and length, not complete MDL including model selection. Controls exploratory; no interpretation asserted."};

}
const book=JSON.parse(fs.readFileSync(process.argv[2] || 'Docs/support/reference/TorahCryptoCorpus20261125/exodus.normalized.json','utf8'));
const words=JSON.parse(fs.readFileSync(process.argv[3] || 'Docs/support/reference/TorahCryptoCorpus20261125/exodus-training-words.json','utf8'));
console.log(JSON.stringify(assay(book,words),null,2));
