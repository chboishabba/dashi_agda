import fs from 'node:fs';
function audit(book,source){
 const R=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3,d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],num=a=>a[0]+3*a[1]+9*a[2];
 const add=(a,b)=>num(d(a).map((x,i)=>mod(x+d(b)[i]))),sub=(a,b)=>num(d(a).map((x,i)=>mod(x-d(b)[i])));
 const mul=(a,b)=>{const x=d(a),y=d(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return num(z.slice(0,3).map(mod))};
 const A=R(27).map(a=>R(27).map(b=>add(a,b))),D=R(27).map(a=>R(27).map(b=>sub(a,b))),M=R(27).map(a=>R(27).map(b=>mul(a,b))),I=R(27).map(x=>x?M[x].indexOf(1):0),all=R(27);
 const gem=Array(27),gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"];for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
 const ix=new Map(gem.map((x,i)=>[x,i])),enc=s=>[...s].map(c=>{if(!ix.has(c))throw Error("glyph");return ix.get(c)});
 const blocks=(lo,hi)=>book.chapters.filter(c=>c.c>=lo&&c.c<=hi).flatMap(c=>{const s=enc(c.verses.map(v=>v.letters).join(""));return R(Math.floor(s.length/216)).map(i=>({rows:[s.slice(i*216,i*216+72),s.slice(i*216+72,i*216+144).reverse(),s.slice(i*216+144,i*216+216)]}))});
 const target={rows:[enc(source.sourceRows[0]),enc(source.sourceRows[1]).reverse(),enc(source.sourceRows[2])]},train=blocks(1,13),test=blocks(16,40);
 function frames(v){const [a,b]=v;return R(72).map(j=>{const pool=[b[j],a[j-1],b[j-1],a[j+1],b[j+1],a[j-2],b[j-2],a[j+2],b[j+2]],k=pool.findIndex(x=>x!==undefined&&x!==a[j]);return k<0?null:{a:a[j],u:D[pool[k]][a[j]],k}})}
 const z=(f,x)=>M[I[f.u]][D[x][f.a]],restore=(f,r)=>A[f.a][M[f.u][r]],compose=(q,p)=>p.map(x=>q[x]),inverse=p=>all.map(x=>p.indexOf(x));
 const map=(f,g,kind)=>all.map(r=>kind==="normalized"?r:kind==="physical"?z(g,restore(f,r)):A[r][z(g,f.a)]);
 function graph(v,kind,selector,twist){
  const fs=frames(v);if(fs.some(x=>!x))return null;
  const tree=R(71).map(j=>({p:j,n:j+1,T:map(fs[j],fs[j+1],kind)}));
  const chords=[];for(let n=1;n<72;n++){let p=-1;if(selector==="repeatA"){for(let j=n-1;j>=0;j--)if(v[0][j]===v[0][n]){p=j;break}}else if(selector==="repeatPair"){for(let j=n-1;j>=0;j--)if(v[0][j]===v[0][n]&&v[1][j]===v[1][n]){p=j;break}}else if(n>=+selector)p=n-(+selector);if(p<0)continue;
   const T=map(fs[n],fs[p],kind);chords.push({p:n,n:p,T:twist?T.map(x=>I[x]):T})}
  return {fs,tree,chords}
 }
 // For deterministic invertible edge constraints on a connected graph, tree transport
 // gives every vertex as a permutation of one root. Chords filter the 27 root states.
 function solve(g){const P=[all];for(const e of g.tree)P.push(compose(e.T,P[e.p]));
  const hol=g.chords.map(e=>compose(inverse(P[e.n]),compose(e.T,P[e.p])));
  const roots=all.filter(r=>hol.every(H=>H[r]===r));
  const paths=roots.map(r=>P.map((p,j)=>restore(g.fs[j],p[r])));
  for(const path of paths)for(const e of g.tree.concat(g.chords))if(e.T[z(g.fs[e.p],path[e.p])]!==z(g.fs[e.n],path[e.n]))throw Error("edge");
  const fixedHistogram={};for(const h of hol){const n=all.filter(r=>h[r]===r).length;fixedHistogram[n]=(fixedHistogram[n]||0)+1}
  return {roots,paths,fixedHistogram}
 }
 function score(b,kind,selector,twist){const g=graph(b.rows.slice(0,2),kind,selector,twist);if(!g)return null;const s=solve(g),truth=b.rows[2],rr=truth.map((x,j)=>z(g.fs[j],x)),ok=e=>e.T[rr[e.p]]===rr[e.n],treePass=g.tree.filter(ok).length,chordPass=g.chords.filter(ok).length;
  return {solutions:s.paths.length,treePass,chordPass,chords:g.chords.length,truth:s.paths.some(p=>p.every((x,j)=>x===truth[j])),singleton:s.paths.length===1?72:0,correct:s.paths.length===1?s.paths[0].filter((x,j)=>x===truth[j]).length:0,output:s.paths.length===1?s.paths[0].map(x=>gem[x]).join(""):null,fixedHistogram:s.fixedHistogram}}
 const results=[];for(const kind of ["normalized","physical","drift"])for(const selector of ["repeatA","repeatPair","13","27"])for(const twist of [false,true]){
  const shem=score(target,kind,selector,twist),summ=bs=>{let n=0,zero=0,one=0,truth=0,correct=0,chordPass=0,chords=0,treePass=0;for(const b of bs){const r=score(b,kind,selector,twist);if(!r)continue;n++;zero+=r.solutions===0;one+=r.solutions===1;truth+=r.truth;correct+=r.correct;chordPass+=r.chordPass;chords+=r.chords;treePass+=r.treePass}return {n,zero,one,truth,correct,chordPass,chords,treePass}};
  results.push({kind,selector,twist,shem,train:summ(train),test:summ(test)})
 }
 // Reverse solve independent return-index selection BEFORE hidden state: from each true r_n,
 // does any earlier return under the specified transport family match true r_p?
 const oracle=[];for(const kind of ["normalized","physical","drift"])for(const twist of [false,true]){
  const g=graph(target.rows.slice(0,2),kind,"repeatA",twist),r=target.rows[2].map((x,j)=>z(g.fs[j],x));let none=0,unique=0,multi=0,choices=0;for(let n=1;n<72;n++){let k=0;for(let p=0;p<n;p++){const v=map(g.fs[n],g.fs[p],kind)[r[n]];k+=r[p]===(twist?I[v]:v)}none+=k===0;unique+=k===1;multi+=k>1;choices+=k}oracle.push({kind,twist,none,unique,multi,choices})}
 return {results,oracle,qualification:"Candidate mandatory permutation constraints on connected tree plus nonlocal chords. F selector nearest repeated visible A/pair or fixed lag13/27; no actual creator gate or recurrence supplied. A physical chart change represents same raw glyph; normalized transport represents same residual. Drift omits scale ratio intentionally as H25 comparator. All C hidden during graph construction and solve; truth only for scoring and separate hindsight oracle. Synthetic chapter blocks and actual Shem regression, not fresh blind holdout. Does not cover general nondeterministic graph or time-evolving return revisits."}
}
const base='Docs/support/reference/TorahCryptoCorpus20261125/';
console.log(JSON.stringify(audit(...['exodus.normalized.json','h20-source-role-residual.json'].map(n=>JSON.parse(fs.readFileSync(base+n,'utf8')))),null,2));
