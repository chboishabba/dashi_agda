import fs from 'node:fs';
function build(book,words){
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

 const orbitMap=new Map();for(let i=0;i<216;i++){const o=[...new Set(perm.map(m=>m[i]))].sort((a,b)=>a-b);orbitMap.set(o.join(","),o)}
 const orbits=[...orbitMap.values()],digits=i=>[i%3,Math.floor(i/3)%3,Math.floor(i/9)],num=d=>d[0]+3*d[1]+9*d[2],mod=x=>(x%3+3)%3;
 const sum=v=>v.reduce((a,i)=>a.map((x,k)=>mod(x+digits(i)[k])),[0,0,0]);
 const partner=(s,x)=>num(s.map((v,k)=>mod(v-digits(x)[k])));
 const byPos=Array(216);orbits.forEach(o=>o.forEach(j=>byPos[j]=o));
 const tri=range(K*K).map(vec);
 for(const r of train)for(let i=2;i<r.seq.length;i++)tri[r.seq[i-2]*K+r.seq[i-1]][r.seq[i]]++;
 const tp=tri.map((a,i)=>normalize(a.map((n,j)=>n+10*transition[i%K][j])));
 const tl=tp.map(a=>a.map(x=>-Math.log2(x)));
 const wc=new Map();for(const w of words)wc.set(w,(wc.get(w)||0)+1);
 const trie={};for(const [w,n] of wc){let node=trie;for(const c of w){node[c]??={};node=node[c]}node.cost=1-Math.log2(n/words.length)}
 const lex=(v,detail=false)=>{const n=v.length,dp=Array(n+1).fill(Infinity),prev=Array(n+1);dp[0]=0;
  for(let i=0;i<n;i++){const offer=(j,c,kind)=>{if(dp[i]+c<dp[j]){dp[j]=dp[i]+c;prev[j]=[i,kind]}};
   offer(i+1,1-Math.log2(prior[v[i]]),"literal");let node=trie;
   for(let j=i;j<n;j++){node=node[alphabet[v[j]]];if(!node)break;if(node.cost!==undefined)offer(j+1,node.cost,"word")}
  }
  if(!detail)return dp[n];let tokens=[];for(let j=n;j>0;){const [i,k]=prev[j];tokens.push({kind:k,text:v.slice(i,j).map(x=>alphabet[x]).join("")});j=i}tokens.reverse();if(tokens.map(x=>x.text).join("")!==v.map(x=>alphabet[x]).join(""))throw Error("lex roundtrip");return {bits:dp[n],tokens};
 };
 function hard(prefix,lexical=false){
  const geo=predict(prefix).geometry,gl=geo.map(x=>x.p.map(p=>-Math.log2(p))),x=prefix.concat(Array(91).fill(-1)),free=[];
  for(const o of orbits){const m=o.filter(j=>j>=125),s=sum(o.filter(j=>j<125).map(j=>prefix[j])).map(v=>mod(-v));
   if(m.length===1)x[m[0]]=num(s);else if(m.length===2){let best=Infinity;for(let v=0;v<K;v++){const w=partner(s,v),c=gl[m[0]-125][v]+gl[m[1]-125][w];if(c<best){best=c;x[m[0]]=v;x[m[1]]=w}}free.push({i:m[0],j:m[1],s})}else throw Error("shape");
  }
  const costAt=k=>tl[x[k-2]*K+x[k-1]][x[k]];
  const score=()=>{let g=0,h=0;for(let k=125;k<216;k++){g+=gl[k-125][x[k]];h+=costAt(k)}return {geometry:g,trigram:h,lexical:lex(x.slice(125)),objective:g+h+(lexical?lex(x.slice(125)):0)}};
  const initial=x.slice(125),before=score();
  for(let pass=0;pass<2;pass++)for(const {i,j,s} of free){
   const affected=[...new Set([i,i+1,i+2,j,j+1,j+2])].filter(k=>k<216);
   const old=x[i];let bv=old,bc=Infinity;
   for(let v=0;v<K;v++){x[i]=v;x[j]=partner(s,v);const c=gl[i-125][x[i]]+gl[j-125][x[j]]+affected.reduce((a,k)=>a+costAt(k),0)+(lexical?lex(x.slice(125)):0);if(c<bc-1e-12){bc=c;bv=v}}
   x[i]=bv;x[j]=partner(s,bv);
  }
  if(orbits.some(o=>sum(o.map(j=>x[j])).some(v=>v)))throw Error("parity");
  const after=score();if(after.objective>before.objective+1e-8)throw Error("objective");
  return {initial,final:x.slice(125),before,after,parity:54};
 }
 // A proper sequential conditional distribution, with identical prefix and previously decoded symbols for all comparators.
 // Geometry from the 125 observed symbols only; soft parity contributes only when all other orbit members are known.
 function predictive(block,geometryPerm=null){
  const prefix=block.slice(0,125),geo=predict(prefix).geometry,acc={trigram:{bits:0,hits:0},geoMix:{bits:0,hits:0},jointSoft:{bits:0,hits:0},unigram:{bits:0,hits:0}};
  let impossible=false,closes=0,correct=0;
  for(let j=125;j<216;j++){
   const t=block[j],q=tp[block[j-2]*K+block[j-1]],g=geo[j-125].p,mid=q.map((v,i)=>.75*v+.25*g[i]);
   const others=byPos[j].filter(k=>k!==j);let z=mid;
   if(others.every(k=>k<j)){closes++;const v=num(sum(others.map(k=>block[k])).map(x=>mod(-x)));correct+=v===t;impossible||=v!==t;z=mid.map((p,i)=>.9*p+.1*(i===v))}
   for(const [name,p] of Object.entries({trigram:q,geoMix:mid,jointSoft:z,unigram:prior})){acc[name].bits-=Math.log2(p[t]);acc[name].hits+=argmax(p)===t}
  }
  return {acc,impossible,closes,correct};
 }
 const trainingLetters=train.reduce((s,r)=>s+r.seq.length,0),width=Math.ceil(Math.log2(trainingLetters+1));
 const wordTableBits=16+wc.size*(4+width)+[...wc.keys()].reduce((s,w)=>s+5*w.length,0); // 16-bit type count, 4-bit length, raw glyphs, fixed width count
 if([...wc.keys()].some(w=>w.length>15)||wc.size>=65536)throw Error("word table width");
 const modelCosts={trainingLetters,countWidth:width,headerAssumption:"shared alphabet, fixed algorithm and dimensions; 3-bit model selector; dense fixed-width count tables; dictionary count + 4-bit length + 5-bit glyphs + count; training not transmitted",unigram:3+K*width,trigram:3+(K+K*K+K*K*K)*width,geoMix:3+(K+K*K+K*K*K+216*K+7*K*K)*width,jointSoft:3+(K+K*K+K*K*K+216*K+7*K*K)*width+2,wordTableBits};
 function benchmark(book,start=1,end=Infinity,runHard=true){
  const seqs=book.chapters.filter(c=>c.c>=start&&c.c<=end).flatMap(c=>blocks([...c.verses.map(v=>v.letters).join("")].map(x=>ix.get(x))));
  const acc=Object.fromEntries(["trigram","geoMix","jointSoft","unigram"].map(n=>[n,{bits:0,hits:0}]));
  let impossible=0,closes=0,correct=0,hardHits=0,mapHits=0,hardCount=0,delta=0,lexDelta=0;
  for(const b of seqs){const p=predictive(b);for(const k in acc){acc[k].bits+=p.acc[k].bits;acc[k].hits+=p.acc[k].hits}impossible+=p.impossible;closes+=p.closes;correct+=p.correct;
    if(runHard){const h=hard(b.slice(0,125));hardCount++;hardHits+=h.final.filter((x,i)=>x===b[125+i]).length;mapHits+=h.initial.filter((x,i)=>x===b[125+i]).length;delta+=h.before.objective-h.after.objective;lexDelta+=h.before.lexical-h.after.lexical}
  }
  const letters=91*seqs.length;for(const k in acc){acc[k].bitsPerLetter=acc[k].bits/letters;acc[k].accuracy=acc[k].hits/letters;acc[k].withModelBits=acc[k].bits+modelCosts[k]}
  return {blocks:seqs.length,letters,acc,hardImpossibleBlocks:impossible,parityClosures:closes,parityCorrect:correct,hardCount,mapHits,hardHits,meanObjectiveDecrease:hardCount?delta/hardCount:null,meanLexicalDecrease:hardCount?lexDelta/hardCount:null};
 }
 function target(){const actual=rows.find(r=>r.c===14).seq.slice(8*216),plain=hard(actual),withLex=hard(actual,true);
  return {plain:{...plain,initial:plain.initial.map(i=>alphabet[i]).join(""),final:plain.final.map(i=>alphabet[i]).join("")},withLex:{...withLex,initial:withLex.initial.map(i=>alphabet[i]).join(""),final:withLex.final.map(i=>alphabet[i]).join(""),tokens:lex(withLex.final,true)}};
 }

 function controls(book,start=1){
  const bs=book.chapters.filter(c=>c.c>=start).flatMap(c=>blocks([...c.verses.map(v=>v.letters).join("")].map(x=>ix.get(x))));
  const scores={trigram:0,unigramMix:0,positionMix:0,geometryMix:0,shuffledPeersMix:0,rotatedPeersMix:0};
  let rng=0x3691553;const rnd=()=>{rng=(Math.imul(rng,1664525)+1013904223)>>>0;return (rng+.5)/4294967296};
  for(const b of bs){
   const pref=b.slice(0,125),sh=pref.slice();for(let i=124;i>0;i--){const j=Math.floor(rnd()*(i+1));[sh[i],sh[j]]=[sh[j],sh[i]]}
   const ge=predict(pref).geometry,gs=predict(sh).geometry,gr=predict(pref.slice(1).concat(pref[0])).geometry;
   for(let j=125;j<216;j++){const t=b[j],q=tp[b[j-2]*K+b[j-1]][t];const probs={trigram:q,unigramMix:.75*q+.25*prior[t],positionMix:.75*q+.25*pos[j][t],geometryMix:.75*q+.25*ge[j-125].p[t],shuffledPeersMix:.75*q+.25*gs[j-125].p[t],rotatedPeersMix:.75*q+.25*gr[j-125].p[t]};for(const k in probs)scores[k]-=Math.log2(probs[k]);}
  }
  return {blocks:bs.length,letters:bs.length*91,bits:scores,bitsPerLetter:Object.fromEntries(Object.entries(scores).map(([k,v])=>[k,v/(bs.length*91)]))};
 }
 return {benchmark,target,modelCosts,controls};
}

const base='Docs/support/reference/TorahCryptoCorpus20261125/';
const load=n=>JSON.parse(fs.readFileSync(base+n+'.normalized.json','utf8'));
const model=build(load('exodus'),JSON.parse(fs.readFileSync(base+'exodus-training-words.json','utf8')));
const names=['exodus','genesis','leviticus','numbers','deuteronomy'];
console.log(JSON.stringify(names.map(n=>({name:n,...model.controls(load(n),n==='exodus'?16:1)})),null,2));
