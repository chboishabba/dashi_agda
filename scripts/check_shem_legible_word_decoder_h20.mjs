import fs from 'node:fs';
function assay(book,words){
 const alphabet=[..."אבגדהוזחטיךכלםמןנסעףפץצקרשת"],K=27,ix=new Map(alphabet.map((c,i)=>[c,i])),range=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3;
 const gem=Array(27),gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"],num=a=>a[0]+3*a[1]+9*a[2],d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)];
 for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
 const fieldIx=new Map(gem.map((c,i)=>[c,i])),toF=alphabet.map(c=>fieldIx.get(c)),fromF=gem.map(c=>ix.get(c));
 const add=(a,b)=>num(d(a).map((x,i)=>mod(x+d(b)[i]))),neg=a=>num(d(a).map(x=>mod(-x))),sub=(a,b)=>add(a,neg(b));
 const mul=(a,b)=>{const x=d(a),y=d(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return num(z.slice(0,3).map(mod))};
 const inv=x=>range(27).find(y=>mul(x,y)===1);
 const ratio=(a,b,c)=>mul(sub(c,a),inv(sub(b,a)));
 const seeds=[22,14],perms=x=>[[x[0],x[1],x[2]],[x[0],x[2],x[1]],[x[1],x[0],x[2]],[x[1],x[2],x[0]],[x[2],x[0],x[1]],[x[2],x[1],x[0]]];
 const roleRatios=[...new Set(seeds.flatMap(r=>perms([0,1,r]).map(x=>ratio(...x))))];if(roleRatios.length!==12)throw Error("role ratio");
 const charseq=c=>[...c.verses.map(v=>v.letters).join("")].map(x=>ix.get(x));
 const train=book.chapters.filter(c=>c.c<=13),prior=Array(K).fill(1),bi=range(K).map(()=>Array(K).fill(0)),tri=range(K*K).map(()=>Array(K).fill(0));
 for(const ch of train){const s=charseq(ch);for(let i=0;i<s.length;i++){prior[s[i]]++;if(i)bi[s[i-1]][s[i]]++;if(i>1)tri[s[i-2]*K+s[i-1]][s[i]]++}}
 const norm=a=>{const sum=a.reduce((s,x)=>s+x,0);return a.map(x=>x/sum)};
 const p=norm(prior),bp=bi.map(a=>norm(a.map((x,i)=>x+10*p[i]))),tp=tri.map((a,j)=>norm(a.map((x,i)=>x+10*bp[j%K][i])));
 // Conditional geometric distribution for the actual mask: B gets only A; C gets A and previously available B.
 // No hidden target value is used. Uniform distinct-anchor marginal for B.
 const makeGeometry=rs=>{
  const map=range(27).map(a=>range(27).map(b=>{if(a===b)return null;return rs.map(r=>fromF[add(toF[a],mul(r,sub(toF[b],toF[a])))])}));
  return (seq,j,shift=0)=>{
   if(j<144){const col=143-j,a=seq[(col+shift)%72];return range(K).map(x=>x===a?0:1/26)}
   const col=j-144,a=seq[(col+shift)%72],b=seq[143-col],vals=map[a][b];return vals?range(K).map(x=>vals.includes(x)?1/vals.length:0):p;
  };
 };
 const geo2=makeGeometry(seeds),geo12=makeGeometry(roleRatios),alpha=.1;
 const models={trigram:null,two:geo2,twelve:geo12,shifted:geo2};
 function score(block){const counts={};for(const [name,geom] of Object.entries(models)){let bits=0,hits=0;for(let j=125;j<216;j++){const q=tp[block[j-2]*K+block[j-1]],g=geom?geom(block,j,name==="shifted"?1:0):null;const prob=g?q.map((x,i)=>(1-alpha)*x+alpha*g[i]):q;if(Math.abs(prob.reduce((s,x)=>s+x,0)-1)>1e-9)throw Error("norm");bits-=Math.log2(prob[block[j]]);hits+=prob.indexOf(Math.max(...prob))===block[j]}counts[name]={bits,hits}}return counts}
 const blocks=book.chapters.filter(c=>c.c>=16).flatMap(c=>{const x=charseq(c);return range(Math.floor(x.length/216)).map(i=>x.slice(i*216,(i+1)*216))});
 const stats=Object.fromEntries(Object.keys(models).map(n=>[n,{bits:0,hits:0}]));
 for(const block of blocks){const result=score(block);for(const n in stats){stats[n].bits+=result[n].bits;stats[n].hits+=result[n].hits}}
 for(const a of Object.values(stats)){a.bitsPerLetter=a.bits/(91*blocks.length);a.accuracy=a.hits/(91*blocks.length)}
 // Train word model only on the existing Exodus 1-13 word table.
 const wc=new Map(),wb=new Map(),wt=new Map(),inc=(m,k)=>m.set(k,(m.get(k)||0)+1),nested=(m,k,w)=>{if(!m.has(k))m.set(k,new Map());inc(m.get(k),w)};
 const clean=words.filter(w=>w.length&&[...w].every(c=>ix.has(c)));for(let i=0;i<clean.length;i++){const w=clean[i];inc(wc,w);if(i)nested(wb,clean[i-1],w);if(i>1)nested(wt,clean[i-2]+" "+clean[i-1],w)}
 const vocab=[...wc.keys()],wi=new Map(vocab.map(w=>[w,[...w].map(c=>ix.get(c))])),base=clean.length+vocab.length,top=(m,n)=>[...m.entries()].sort((a,b)=>b[1]-a[1]||a[0].localeCompare(b[0],"he")).slice(0,n).map(x=>x[0]);
 const common=top(wc,28),tot=m=>m?[...m.values()].reduce((s,x)=>s+x,0):0;
 const cache=new Map();
 function next(u,v){const key=u+" "+v;if(cache.has(key))return cache.get(key);const b=wb.get(v),t=wt.get(key),bn=tot(b),tn=tot(t),cands=[...new Set([...common,...top(b||new Map(),24),...top(t||new Map(),24)])];
  const out=cands.map(w=>{const q0=(wc.get(w)+1)/base,q1=((b?.get(w)||0)+5*q0)/(bn+5),q2=((t?.get(w)||0)+3*q1)/(tn+3);return [w,-Math.log2(q2)]});cache.set(key,out);return out}
 // Infer last two words from observed suffix only, using longest dictionary suffix.
 function context(pref){let s=pref.map(i=>alphabet[i]).join(""),out=[];for(let j=0;j<2;j++){const w=vocab.filter(w=>s.endsWith(w)).sort((a,b)=>b.length-a.length||(wc.get(b)-wc.get(a)))[0]||"";out.unshift(w);s=s.slice(0,s.length-w.length)}return out}
 function beam(prefix,geom,shift=0){
  const [u,v]=context(prefix),bins=range(92).map(()=>[]);bins[0]=[{words:[],seq:prefix.slice(),u,v,cost:0,wordCost:0,geometryDelta:0,charCost:0}];
  for(let n=0;n<91;n++){
   const keep=bins[n].sort((a,b)=>a.cost-b.cost).slice(0,24);bins[n]=[];
   for(const st of keep)for(const [w,wcost] of next(st.u,st.v)){
    const letters=wi.get(w),end=n+letters.length;if(end>91)continue;
    // explicit anti-loop heuristic, not a probability model: no repeated 3-word phrase.
    if(st.words.some((z,i)=>i+2<st.words.length&&z===st.u&&st.words[i+1]===st.v&&st.words[i+2]===w))continue;
    const seq=st.seq.slice();let delta=0,cc=0;for(const x of letters){const j=seq.length,q=tp[seq[j-2]*K+seq[j-1]],g=geom?geom(seq,j,shift):null;cc-=Math.log2(q[x]);if(g)delta-=Math.log2(((1-alpha)*q[x]+alpha*g[x])/q[x]);seq.push(x)}
    const wordCost=st.wordCost+wcost,charCost=st.charCost+cc,geometryDelta=st.geometryDelta+delta,cost=wordCost+.25*charCost+geometryDelta;
    bins[end].push({words:st.words.concat(w),seq,u:st.v,v:w,cost,wordCost,charCost,geometryDelta});if(bins[end].length>240)bins[end]=bins[end].sort((a,b)=>a.cost-b.cost).slice(0,48);
   }
  }
  const best=bins[91].sort((a,b)=>a.cost-b.cost).slice(0,3);if(!best.length)throw Error("beam empty");return best.map(b=>({text:b.words.join(" "),letters:b.seq.slice(125).map(i=>alphabet[i]).join(""),cost:b.cost,wordCost:b.wordCost,charCost:b.charCost,geometryDelta:b.geometryDelta}));
 }
 const last=charseq(book.chapters.find(c=>c.c===14)).slice(1728);if(last.length!==125)throw Error("prefix");const output={};
 for(const [name,g] of Object.entries(models))output[name]=beam(last,g,name==="shifted"?1:0);
 // Unblind only after candidate generation.
 const truth=charseq(book.chapters.find(c=>c.c===15)).slice(0,91);const actual=truth.map(i=>alphabet[i]).join("");
 for(const candidates of Object.values(output))for(const c of candidates){c.hits=[...c.letters].filter((x,i)=>x===actual[i]).length;if(c.letters.length!==91)throw Error("length")}
 return {source:"pinned existing WLC Exodus corpus; synthetic 91-letter continuation after chapter 14",training:{chapters:[1,13],words:clean.length,vocabulary:vocab.length},heldout:{chapters:[16,40],blocks:blocks.length,letters:91*blocks.length,teacherForced:stats,qualification:"reused exploratory holdout; not blind beam accuracy"},context:context(last),prefix:last.map(i=>alphabet[i]).join(""),ratioSheets:roleRatios,parameters:{alpha,beam:24,charWeight:.25,noRepeatedTrigramWords:true,wordModel:"interpolated word trigram, heuristic beam ranking; not normalized word model code"},output,actual,qualification:"generated candidates restricted to training vocabulary, not translation, recovered manuscript, or established cipher; no target suffix consulted during generation"};
}
const base='Docs/support/reference/TorahCryptoCorpus20261125/';
console.log(JSON.stringify(assay(JSON.parse(fs.readFileSync(base+'exodus.normalized.json','utf8')),JSON.parse(fs.readFileSync(base+'exodus-training-words.json','utf8'))),null,2));
