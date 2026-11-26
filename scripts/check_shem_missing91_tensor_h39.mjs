import fs from 'node:fs';
function audit(book,old){
const V=Array.from({length:27},(_,i)=>i),R=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3,d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],num=a=>a[0]+3*a[1]+9*a[2],A=V.map(a=>V.map(b=>num(d(a).map((x,i)=>mod(x+d(b)[i]))))),D=V.map(a=>V.map(b=>num(d(a).map((x,i)=>mod(x-d(b)[i])))));
const glyphs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"],gem=Array(27);for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=glyphs[i]}const ix=new Map(gem.map((g,i)=>[g,i])),enc=s=>[...s].map(g=>ix.get(g)),str=s=>s.map(x=>gem[x]).join("");
const coords=R(3).flatMap(g=>R(4).flatMap(h=>R(6).map(k=>[g,h,k]))),parents=coords.map((p,i)=>coords.map((q,j)=>j!==i&&q.every((v,k)=>v===0||v===p[k])?j:-1).filter(j=>j>=0)), masks=coords.map(([g,h,k])=>+(g!==0)+2*(h!==0)+4*(k!==0)),sum=xs=>xs.reduce((a,b)=>A[a][b],0);
const seq=ch=>enc(ch.verses.map(v=>v.letters).join("")),blocks=(lo,hi)=>book.chapters.filter(ch=>ch.c>=lo&&ch.c<=hi).flatMap(ch=>{let s=seq(ch);return R(Math.floor(s.length/216)).map(j=>s.slice(j*216,j*216+216))}),train=blocks(1,13),test=blocks(16,40);
const pref=seq(book.chapters.find(ch=>ch.c===14)).slice(1728);if(str(pref)!==old.prefix||pref.length!==125)throw Error("mask");
 // Physical sequence order. B is decoded in reverse column order, so use a reversed slot traversal for its anchored chart.
 // For B anchor at physical position 72, C anchor at 144. Each role has a causal tensor synthesis.
 function info(s,j,shift=0){let role=Math.floor(j/72),k=j%72;let anchor=role===1?s[(71-k+shift)%72]:role===2?s[143-((k+shift)%72)]:0;
 let base=role===0?0:anchor;let par=parents[k].map(i=>{let t=role*72+i;let p=role===1?s[(71-i+shift)%72]:role===2?s[143-((i+shift)%72)]:0;return D[s[t]][p]});
 // z_j = raw residual minus reconstructed proper-parent coefficients, not raw parents.
 let zs=[];for(let i=0;i<=k;i++){let t=role*72+i,p=role===1?s[(71-i+shift)%72]:role===2?s[143-((i+shift)%72)]:0,off=A[p][sum(parents[i].map(q=>zs[q]))];if(i===k)return {role,k,off,anchor,mask:masks[k]};zs.push(D[s[t]][off])}
 }
 const prior=Array(27).fill(1),bi=R(27).map(()=>Array(27).fill(0)),tri=R(729).map(()=>Array(27).fill(0));for(const ch of book.chapters.filter(c=>c.c<=13)){let s=seq(ch);s.forEach((x,i)=>{prior[x]++;if(i)bi[s[i-1]][x]++;if(i>1)tri[s[i-2]*27+s[i-1]][x]++})}
 const norm=x=>{let t=x.reduce((a,b)=>a+b,0);return x.map(v=>v/t)},p=norm(prior),bp=bi.map(x=>norm(x.map((v,i)=>v+10*p[i]))),tp=tri.map((x,i)=>norm(x.map((v,j)=>v+10*bp[i%27][j])));
 const keys=(f,kind)=>kind==="sector"?f.role+":"+f.mask:kind==="anchor"?f.role+":"+f.mask+":"+f.anchor:f.role+"";
 function fit(shift){let tables=new Map();for(const s of train)for(let j=72;j<216;j++){let f=info(s,j,shift),z=D[s[j]][f.off];for(const kind of ["role","sector","anchor"]){let k=kind+keys(f,kind),t=tables.get(k)||Array(27).fill(0);t[z]++;tables.set(k,t)}}return tables}
 const fits=[fit(0),fit(1)];function probs(s,j,mode){let q=tp[s[j-2]*27+s[j-1]];if(mode==="language")return q;if(mode==="unigram")return p;let shift=mode==="shift"?1:0,f=info(s,j,shift),tab=fits[shift],z=norm(tab.get("role"+keys(f,"role")).map(v=>v+1));for(const kind of ["sector","anchor"]){let t=tab.get(kind+keys(f,kind));if(t)z=norm(t.map((v,i)=>v+20*z[i]))}let g=V.map(x=>z[D[x][f.off]]);if(mode==="tensor")return g;return q.map((v,i)=>.8*v+.2*g[i])}
 const modes=["unigram","language","tensor","joint","shift"],results={};for(const mode of modes){let hits=0,bits=0,freeHits=0,exact=0;for(const s of test){let gen=s.slice(0,125);for(let j=125;j<216;j++){let q=probs(s,j,mode);hits+=q.indexOf(Math.max(...q))===s[j];bits-=Math.log2(q[s[j]]);let r=probs(gen,j,mode);gen.push(r.indexOf(Math.max(...r)))}let h=gen.slice(125).filter((v,i)=>v===s[125+i]).length;freeHits+=h;exact+=h===91}
 // character beam, not restricted to complete training words. All hypotheses use only generated past.
 let beam=[{s:pref.slice(),cost:0}];for(let j=125;j<216;j++){let next=[];for(const b of beam){let q=probs(b.s,j,mode);for(const x of V)next.push({s:b.s.concat(x),cost:b.cost-Math.log2(q[x])})}next.sort((a,b)=>a.cost-b.cost);beam=next.slice(64)}
 results[mode]={teacher:{hits,bits,n:91*test.length},free:{hits:freeHits,exact},candidates:beam.slice(0,3).map(b=>({text:str(b.s.slice(125)),cost:b.cost}))}}
 // score only after generation. This target was disclosed historically; regression not blind.
 const truth=seq(book.chapters.find(ch=>ch.c===15)).slice(0,91);for(const r of Object.values(results))for(const b of r.candidates){b.hits=enc(b.text).filter((x,i)=>x===truth[i]).length}
 // exact residual patch for original mask using the new causal chart (target-derived).
 let s=pref.slice(),patch=[];for(let j=125;j<216;j++){let f=info(s,j),z=D[truth[j-125]][f.off];patch.push(z);s.push(A[f.off][z])}if(str(s.slice(125))!==str(truth))throw Error("patch");
 return {prefix:str(pref),truth:str(truth),train:train.length,test:test.length,results,patch:{coordinates:patch,restored:str(s.slice(125)),exact:91},qualification:"Original H20 synthetic 125/91 mask, crossing chapter14/15. B physical scan uses visible A reversed; C uses reconstructed B reversed. Same causal anchored 3x4x6 chart in each role, predicted residual distribution learned only Exodus1-13; no hidden target read in generation. Teacher-forced and free greedy regression on 175 reused chapter blocks; 64-wide character beam on actual continuation. Joint fixed .8 language + .2 geometry mixture, shifted control retrained. Exact patch extracted from known target is BIDI, not independent recovery. Character beam can produce nonwords; not fresh blind. No real manuscript lacuna."}
}
const base='Docs/support/reference/TorahCryptoCorpus20261125/';console.log(JSON.stringify(audit(...['exodus.normalized.json','h20-legible-word-decoder.json'].map(n=>JSON.parse(fs.readFileSync(base+n,'utf8')))),null,2));
