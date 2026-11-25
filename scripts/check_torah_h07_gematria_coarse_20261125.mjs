import fs from 'node:fs';
function chartChecks(){
 const R=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3,d=i=>[i%3,Math.floor(i/3)%3,Math.floor(i/9)],num=a=>a[0]+3*a[1]+9*a[2];
 const glyphs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"], alphabet=Array(27);
 const phase=(x,k=1)=>num(d(x).map(v=>mod(v+k)));
 for(let i=0;i<27;i++){const t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);alphabet[num([t,mod(t+u),mod(t+v)])]=glyphs[i]}
 const records=glyphs.map((c,i)=>({glyph:c,value:(i%9+1)*10**Math.floor(i/9),index:alphabet.indexOf(c),digits:d(alphabet.indexOf(c)),next:alphabet[phase(alphabet.indexOf(c))]}));
 for(let i=0;i<27;i++){const x=alphabet.indexOf(glyphs[i]);if(alphabet[phase(x)]!==glyphs[(i+9)%27]||alphabet[x]!==glyphs[i])throw Error("glyph chart")}
 const units=[[1,0],[0,1],[-1,-1]],mul=([a,b],[c,d])=>[a*c-b*d,a*d+b*c-b*d],norm=([a,b])=>a*a-a*b+b*b,conj=([a,b])=>[a-b,-b];
 const group=R(6).map(i=>({t:i%3,s:Math.floor(i/3),z:units[i%3].map(v=>Math.floor(i/3)?-v:v)}));
 for(const a of group)for(const b of group){const c=mul(a.z,b.z),target=group.find(x=>x.z.join()==c.join());if(!target||target.t!==(a.t+b.t)%3||target.s!==(a.s^b.s)||norm(c)!==1)throw Error("unit product")}
 for(const a of group){if(conj(a.z).join()!=group.find(x=>x.t===mod(-a.t)&&x.s===a.s).z.join())throw Error("conjugation")}
 const coarseCounts=Array(54).fill(0);let n=0;
 const coarse=(m,s,a,b,c)=>{const [t,u,v]=d(c);return 27*s+9*t+3*mod(v-t)+mod(u-t)};
 for(let m=0;m<5;m++)for(let s=0;s<2;s++)for(let a=0;a<27;a++)for(let b=0;b<27;b++)for(let c=0;c<27;c++){const k=coarse(m,s,a,b,c),q=coarse(m,s,a,b,phase(c));if(q!==27*s+9*((Math.floor(k%27/9)+1)%3)+k%9)throw Error("coarse phase");coarseCounts[k]++;n++}
 if(coarseCounts.some(x=>x!==3645))throw Error("fibre");
 return {alphabet:alphabet.join(""),records,geometry:{fine:n,coarse:54,perFibre:3645,phaseSquares:n,coarseActiveFixed:0,coarseActiveOrbits:18,coarseIdentityFixed:54,unitProducts:36,unitConjugations:6},obstructions:{R13:"1+2*13 vs 9*3; no bijective conjugacy",frobenius:"3 fixed +8*3 vs 9*3; no bijective conjugacy",finalSwap:"17 fixed +5*2 vs additive negation 1 fixed+13*2; no bijective conjugacy",fixedCoarse:"active quotient and identity action distinct; fixed quotient fibres would have to union whole phase orbits; 3645 is divisible by 3 but this particular quotient is not constant on orbits"}};
}
function run(books,alphabetChart){
 const alphabet=[...alphabetChart],K=27,R=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3,d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],num=x=>x[0]+3*x[1]+9*x[2],marks=R(5).flatMap(i=>R(5).filter(j=>j>i).map(j=>[i,j])),mark=(m,h)=>[(m-h+5)%5,(m+h)%5].sort((a,b)=>a-b),frame=R(10).map(j=>marks.findIndex(p=>p.join()==mark(j%5,1+Math.floor(j/5)).join())),comp=p=>R(5).filter(i=>!p.includes(i)),w=p=>R(5).map(i=>+!p.includes(i)),eq=(a,b)=>a.join()==b.join();
 function pack(p,a,b,c){const v=R(5).map(()=>0),u=v.slice(),o=v.slice();v[p[0]]=1;u[p[1]]=1;comp(p).forEach((j,k)=>{v[j]=a[k];u[j]=b[k];o[j]=c[k]});return [v,u,o]}
 function chart(v,u,o,p){const [i,j]=p,D=mod(v[i]*u[j]-v[j]*u[i]);if(!D)return null;const a=v.map((x,k)=>mod(D*(u[j]*x-v[j]*u[k]))),b=v.map((x,k)=>mod(D*(v[i]*u[k]-u[i]*x))),c=o.map((z,k)=>mod(z-o[i]*a[k]-o[j]*b[k]));return [a,b,c]}
 const proj=(x,a,b,p)=>x.map((z,k)=>mod(z-x[p[0]]*a[k]-x[p[1]]*b[k]));
 const offset=(x,p)=>num(comp(p).map(i=>x[i])), shift=(x,k=1)=>num(d(x).map(v=>mod(v+k)));
 let checks=0,seams=0,zero=0,cocycle=0,phase=0,rotation=0;const cache=[];
 for(let m=0;m<10;m++)for(let a=0;a<K;a++)for(let b=0;b<K;b++){
  const p=marks[m],[v,u]=pack(p,d(a),d(b),[0,0,0]),ad=marks.map(q=>chart(v,u,[0,0,0,0,0],q)),qidx=ad.findIndex(x=>x),q=marks[qidx],[aq,bq]=ad[qidx],key=[qidx,offset(aq,q),offset(bq,q)].join(",");
  const dp=proj(w(p),aq,bq,q),res=dp.map((x,i)=>mod(x-w(q)[i]));
  const cmap=R(K).map(c=>offset(proj(pack(p,d(a),d(b),d(c))[2],aq,bq,q),q));
  if(new Set(cmap).size!==27)throw Error("offset bijection");
  for(let c=0;c<K;c++){
   const z=cmap[c],back=chart(aq,bq,pack(q,[0,0,0],[0,0,0],d(z))[2],p);
   if(offset(back[2],p)!==c)throw Error("inverse");
   const transported=offset(proj(pack(p,d(a),d(b),d(shift(c)))[2],aq,bq,q),q);
   if(transported!==num(d(z).map((x,i)=>mod(x+d(offset(dp,q))[i]))))throw Error("seam phase");
   checks++;phase++;
   if(shift(shift(shift(c)))!==c||shift(c)===c)throw Error("phase order");
  }
  const pi=[0,1,4,2,3],inv=R(5).map(i=>pi.indexOf(i)),rp=p.map(i=>pi[i]).sort((x,y)=>x-y);
  // Ambient rotation moves pivot mark and slopes as well as offset.
  const rot=(c)=>chart(...pack(p,d(a),d(b),d(c)).map(x=>inv.map(i=>x[i])),rp);
  for(const c of [0,1,3,9]){const r=rot(c),s=rot(shift(c));if(!eq(s[2],r[2].map((x,i)=>mod(x+w(rp)[i]))))throw Error("rotation covariance");rotation++}
  if(qidx!==m){seams++;zero+=res.every(x=>!x)}
  for(let ri=0;ri<10;ri++)if(ad[ri]){const r=marks[ri],[ar,br]=ad[ri],qr=proj(w(q).map((x,i)=>mod(x-w(r)[i])),ar,br,r),pr=proj(w(p).map((x,i)=>mod(x-w(r)[i])),ar,br,r);if(!eq(proj(res,ar,br,r).map((x,i)=>mod(x+qr[i])),pr))throw Error("cocycle");cocycle++}
  cache.push({key,cmap,delta:offset(dp,q),plainDelta:offset(w(q),q)});
 }
 const entry=(m,a,b)=>cache[(m*K+a)*K+b],v0=()=>R(K).map(()=>0),norm=x=>{const n=x.reduce((a,b)=>a+b,0);return x.map(v=>v/n)},addCount=(map,k,v)=>{if(!map.has(k))map.set(k,v0());map.get(k)[v]++};
 const toseq=c=>[...c.verses.map(v=>v.letters).join("")].map(x=>{let i=alphabet.indexOf(x);if(i<0)throw Error("glyph");return i});
 const blocks=(book,lo=1,hi=999)=>book.chapters.filter(c=>c.c>=lo&&c.c<=hi).flatMap(c=>{const s=toseq(c);return R(Math.floor(s.length/216)).map(i=>s.slice(i*216,i*216+216))});
 const train=blocks(books.exodus,1,13),prior=norm(train.flat().reduce((a,x)=>(a[x]++,a),R(K).map(()=>1))),pair=new Map(),canonical=new Map(),scrambled=new Map(),coarse=new Map();
 const col=(b,j)=>[b[j],b[143-j],b[144+j]],controlMark=j=>frame[(7*j+3)%10];
 for(const b of train)for(let j=0;j<72;j++){const [a,v,c]=col(b,j),e=entry(frame[j%10],a,v),s=entry(controlMark(j),a,v);addCount(coarse,Math.floor((j%10)/5),c);addCount(pair,a*K+v,c);addCount(canonical,e.key,e.cmap[c]);addCount(scrambled,s.key,s.cmap[c])}
 const group=(e,c,delta)=>num(d(e.cmap[c]).map((x,i)=>mod(x+d(delta)[i]))),count=(map,k)=>map.get(k)||v0();
 function pred(a,b,j){
  const e=entry(frame[j%10],a,b),s=entry(controlMark(j),a,b),n=count(canonical,e.key),np=count(pair,a*K+b),ns=count(scrambled,s.key),smooth=(arr)=>norm(arr.map((x,i)=>x+10*prior[i]));
  const raw=smooth(e.cmap.map(c=>n[c])),pool=delta=>smooth(R(K).map(c=>(n[e.cmap[c]]+n[group(e,c,delta)]+n[group(e,c,num(d(delta).map(x=>mod(2*x))))])/3));
  const co=smooth(count(coarse,Math.floor((j%10)/5))),fine=pool(e.delta);return {unigram:prior,pair:smooth(np),h07:raw,h07Phase:fine,uncorrectedPhase:pool(e.plainDelta),relabelControl:smooth(s.cmap.map(c=>ns[c])),coarse:co,fineCoarse:co.map((x,i)=>(x+fine[i])/2)};
 }
 const keys=["unigram","pair","h07","h07Phase","uncorrectedPhase","relabelControl","coarse","fineCoarse"];
 function score(bs){const scores=Object.fromEntries(keys.map(k=>[k,{bits:0,hits:0}]));let n=0;for(const b of bs)for(let j=19;j<72;j++){const [a,v,c]=col(b,j),p=pred(a,v,j);n++;for(const k of keys){const q=p[k];scores[k].bits-=Math.log2(q[c]);scores[k].hits+=q.indexOf(Math.max(...q))===c}}for(const s of Object.values(scores))s.bitsPerLetter=s.bits/n;return {blocks:bs.length,letters:n,scores}}
 const results={};for(const [name,b] of Object.entries(books))results[name]=score(blocks(b,name==="exodus"?16:1));
 const rows=books.exodus.chapters.find(c=>c.c===14).verses.filter(v=>v.v>=19&&v.v<=21).map(v=>[...v.letters].map(x=>alphabet.indexOf(x))).flat();
 const target=score([rows]),prefix=toseq(books.exodus.chapters.find(c=>c.c===14)).slice(1728);
 const candidate=[];for(let j=0;j<72;j++){const a=prefix[j],b=prefix[143-j];let q;if(b!==undefined)q=pred(a,b,j).h07Phase;else{q=v0();for(let v=0;v<K;v++){const p=pred(a,v,j).h07Phase;for(let c=0;c<K;c++)q[c]+=prior[v]*p[c]}}candidate.push(alphabet[q.indexOf(Math.max(...q))])}
 const completion=R(19).map(()=>alphabet[prior.indexOf(Math.max(...prior))]).join("")+candidate.join("");
 return {geometry:{markedStates:checks,phaseSquares:phase,rotationBasisCovariance:rotation,canonicalSeams:seams,zeroSeams:zero,cocycle,canonicalDirections:new Set(cache.map(e=>e.key)).size},training:{blocks:train.length,triples:72*train.length,canonicalDirections:canonical.size},results,shem:target,completion:{text:completion,length:completion.length,knownB:53,unobservedB:19,qualification:"synthetic pointwise marginal MAP, not joint optimum or restored text"},notes:"Actual donor pack/chart/projection and phase convention transcribed. Alphabet ordinal and cyclic column mark are chosen adapters, not source semantics. 53 third-row glyphs with both observed inputs (raw prefix 125); no teacher forcing. Scores matched on same symbols; comparison to earlier whole-suffix score invalid. Pair smoothing uses shared training unigram, phase pooling averages counts under corrected action then adds original prior; not strict phase-invariant probability. Relabel control is a second fixed chart labeling, not morphology permutation. No model cost included; heldout books already used in prior experiments, exploratory."};
}
const base='Docs/support/reference/TorahCryptoCorpus20261125/';
const books=Object.fromEntries(['exodus','genesis','leviticus','numbers','deuteronomy'].map(n=>[n,JSON.parse(fs.readFileSync(base+n+'.normalized.json','utf8'))]));
const chart=chartChecks(),assay=run(books,chart.alphabet),letters=Object.values(assay.results).reduce((s,b)=>s+b.letters,0),weighted=Object.fromEntries(Object.keys(assay.shem.scores).map(k=>[k,Object.values(assay.results).reduce((s,b)=>s+b.scores[k].bits,0)/letters]));console.log(JSON.stringify({chart,assay,weighted,letters},null,2));
