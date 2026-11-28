import fs from 'node:fs';
function operators(books){
 const raw=[..."אבגדהוזחטיךכלםמןנסעףפץצקרשת"],std=[..."אבגדהוזחטיכלמנסעפצקרשת"],fold=c=>({"ך":"כ","ם":"מ","ן":"נ","ף":"פ","ץ":"צ"})[c]??c;
 const R=n=>Array.from({length:n},(_,i)=>i),idx=c=>raw.indexOf(c),mod=x=>((x%3)+3)%3,d=i=>[i%3,Math.floor(i/3)%3,Math.floor(i/9)],num=a=>a[0]+3*a[1]+9*a[2],add=(...vs)=>R(3).map(i=>mod(vs.reduce((s,v)=>s+v[i],0)));
 // same field as H3, t^3=t+1; Frobenius inverse is square.
 const mul=(a,b)=>{const z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=a[i]*b[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return z.slice(0,3).map(mod)};
 const F=x=>mul(mul(x,x),x),F2=x=>F(F(x)),neg=x=>x.map(v=>mod(-v));
 const ops={atbash:c=>std[21-std.indexOf(fold(c))],albam:c=>std[(std.indexOf(fold(c))+11)%22]};
 for(const c of std)for(const f of Object.values(ops))if(f(f(c))!==c)throw Error("involution");
 for(const i of R(27))if(num(F(F2(d(i))))!==i)throw Error("F order");
 const training=books.exodus.chapters.filter(c=>c.c<=13).flatMap(c=>c.verses.map(v=>v.letters)).join("");
 const prior=raw.map(c=>1+[...training].filter(x=>x===c).length),N=prior.reduce((a,b)=>a+b,0),p=prior.map(n=>n/N);
 const foldedPrior=std.map(c=>raw.reduce((s,x,i)=>s+(fold(x)===c?p[i]:0),0));
 const specs=[["exodus",14,19],["deuteronomy",32,6],["genesis",36,32],["exodus",20,13]];
 let rng=0x14369;const rnd=()=>{rng=(Math.imul(rng,1664525)+1013904223)>>>0;return (rng+.5)/4294967296};
 const shuffle=a=>{a=a.slice();for(let i=a.length-1;i>0;i--){let j=Math.floor(rnd()*(i+1));[a[i],a[j]]=[a[j],a[i]]}return a};
 const metric=(a,b,c)=>{
   let M={};const n=a.length,k=Math.round(3*n*125/216)-n;
   for(const [name,f] of Object.entries(ops)){let total=0,hit=0,pred=[];for(let j=0;j<n;j++){const v=f(a[j]);pred.push(v);hit+=v===fold(c[j]);total++}M[name]={hits:hit,n:total};}
   const tests=[["additive",(x,y)=>neg(add(x,y))],["frobenius",(x,y)=>F(neg(add(x,F(y))))]];
   for(const [name,f] of tests){let hit=0,erasedHit=0,code=0,base=0;for(let j=0;j<n;j++){
    const guess=num(f(d(idx(a[j])),d(idx(b[j])))),t=idx(c[j]);hit+=guess===t;
    if(j<k){erasedHit+=guess===t;const q=.5*p[t]+.5*(guess===t);code-=Math.log2(q);base-=Math.log2(p[t]);}
   }M[name]={hits:hit,n,erasureHits:erasedHit,erasureN:k,softBitsPerPredicted:code/k,unigramBitsPerPredicted:base/k};}
   return M;
 };
 const results=specs.map(([book,ch,v])=>{
  const vs=books[book].chapters.find(c=>c.c===ch).verses.filter(x=>x.v>=v&&x.v<=v+2),[a,b0,c]=vs.map(x=>[...x.letters]),b=b0.slice().reverse(),n=a.length;
  if(b.length!==n||c.length!==n)throw Error("length");
  const observed=metric(a,b,c),nulls=R(1000).map(()=>metric(a,shuffle(b),shuffle(c)));
  const comparisons=Object.fromEntries(Object.keys(observed).map(k=>[k,{...observed[k],nullMeanHits:nulls.reduce((s,x)=>s+x[k].hits,0)/nulls.length,nullAtLeast:nulls.filter(x=>x[k].hits>=observed[k].hits).length}]));
  return {book,ch,v,rowLength:n,observedCount:Math.round(3*n*125/216),missingCount:3*n-Math.round(3*n*125/216),comparisons};
 });
 // Alphabet exact fibre: folded letter plus final flag only for five paired forms, zero remains a field coordinate not missing.
 let roundtrips=0;for(const c of raw){const pair=[fold(c),fold(c)!==c],reverse=pair[1]?raw.find(x=>x!==pair[0]&&fold(x)===pair[0]):pair[0];if(reverse!==c)throw Error("fold");roundtrips++}
 return {field:"F3[t]/(t^3-t-1)",alphabetRoundtrips:roundtrips,foldedAlphabet:22,finalFlags:5,results,notes:"Exploratory fixed operators, raw parity versus folded traditional involutions, not directly comparable. A fully observed, B first k observed in reversed chart, C all missing, B remainder missing. Only k C symbols have two observed operands for additive/Frobenius; Atbash/Albam predict C from A. Full-column hits are diagnostic, not holdout. Shuffles preserve row marginals, not morphology. Soft score 50% hard guess plus 50% training unigram, only scored on k C symbols; not full suffix MDL. Windows already selected; no significance or source intent claim."};
}
const base='Docs/support/reference/TorahCryptoCorpus20261125/';
const books=Object.fromEntries(['genesis','exodus','deuteronomy'].map(n=>[n,JSON.parse(fs.readFileSync(base+n+'.normalized.json','utf8'))]));
console.log(JSON.stringify(operators(books),null,2));
