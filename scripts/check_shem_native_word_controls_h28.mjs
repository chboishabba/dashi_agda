import fs from 'node:fs';
function audit(fixtures){
 const R=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3,d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],num=a=>a[0]+3*a[1]+9*a[2];
 const sub=(a,b)=>num(d(a).map((x,i)=>mod(x-d(b)[i]))),neg=a=>sub(0,a);
 const mul=(a,b)=>{const x=d(a),y=d(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return num(z.slice(0,3).map(mod))};
 const inv=x=>{if(!x)throw Error("zero");return R(27).find(y=>mul(x,y)===1)};
 const ratio=(a,b,c)=>mul(sub(c,a),inv(sub(b,a)));
 const perms=x=>[[x[0],x[1],x[2]],[x[0],x[2],x[1]],[x[1],x[0],x[2]],[x[1],x[2],x[0]],[x[2],x[0],x[1]],[x[2],x[1],x[0]]];
 const powers=[1];for(let i=1;i<13;i++)powers.push(mul(powers[i-1],3));
 const relation=[];for(let k=0;k<13;k++)for(const e of [1,-1])for(let f=0;f<2;f++)relation.push([[0,1],[1,1],[5,0]].map(([j,s])=>{const x=powers[(k+e*j+13)%13];return s^f?neg(x):x}));
 const direct=new Set(relation.map(t=>t.join())),unordered=new Set(relation.flatMap(perms).map(t=>t.join())),two=new Set(relation.map(x=>ratio(...x))),twelve=new Set(relation.flatMap(perms).map(x=>ratio(...x)));
 if(direct.size!==52||unordered.size!==312||two.size!==2||twelve.size!==12)throw Error("donor relation");
 const gem=Array(27),gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"];for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
 const ix=new Map(gem.map((x,i)=>[x,i])),enc=s=>[...s].map(x=>{if(!ix.has(x))throw Error("glyph");return ix.get(x)});
 function stat(a,b,c){const out={ordered:0,unordered:0,two:0,twelve:0,degenerate:0,allEqual:0};for(let j=0;j<a.length;j++){const t=[a[j],b[j],c[j]],key=t.join();out.ordered+=direct.has(key);out.unordered+=unordered.has(key);if(a[j]===b[j]){out.degenerate++;out.allEqual+=a[j]===c[j]}else{const r=ratio(...t);out.two+=two.has(r);out.twelve+=twelve.has(r)}}return out}
 // Shift or reorder whole source word tokens of C only; A/B untouched, same complete target set.
 let seed=0x280369;const rnd=()=>{seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return (seed>>>0)/4294967296};
 const shuf=a=>{a=a.slice();for(let i=a.length-1;i>0;i--){let j=Math.floor(rnd()*(i+1));[a[i],a[j]]=[a[j],a[i]]}return a};
 const summarise=(values,truth)=>Object.fromEntries(["ordered","unordered","two","twelve"].map(k=>[k,{observed:truth[k],mean:values.reduce((s,x)=>s+x[k],0)/values.length,atLeast:values.filter(x=>x[k]>=truth[k]).length,n:values.length,min:Math.min(...values.map(x=>x[k])),max:Math.max(...values.map(x=>x[k]))}]));
 return fixtures.map(f=>{
  const words=f.rows.map(r=>r.words.map(w=>w.glyphs)),a=enc(words[0].join("")),b=enc(words[1].join("")).reverse(),c=enc(words[2].join(""));if(a.length!==b.length||a.length!==c.length)throw Error("length");
  const observed=stat(a,b,c),wordOrder=R(words[2].length).map(j=>stat(a,b,enc(words[2].slice(j).concat(words[2].slice(0,j)).join(""))));
  const random=R(4096).map(()=>stat(a,b,enc(shuf(words[2]).join(""))));
  const glyphShift=R(c.length).map(j=>stat(a,b,c.slice(j).concat(c.slice(0,j))));
  return {book:f.book,chapter:f.ch,verse:f.v,length:a.length,wordCounts:words.map(w=>w.length),observed,wordRotation:summarise(wordOrder,observed),wordShuffle:summarise(random,observed),glyphRotation:summarise(glyphShift,observed)};
 });
}
const fixtures=JSON.parse(fs.readFileSync('Docs/support/reference/TorahCryptoCorpus20261125/h28-native-word-fixture.json','utf8'));console.log(JSON.stringify(audit(fixtures),null,2));
