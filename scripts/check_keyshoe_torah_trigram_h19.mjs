import fs from 'node:fs';
function assay(books){
 const R=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3,d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],num=a=>a[0]+3*a[1]+9*a[2],add=(a,b)=>num(d(a).map((x,i)=>mod(x+d(b)[i]))),neg=a=>num(d(a).map(x=>mod(-x))),sub=(a,b)=>add(a,neg(b));
 const mul=(a,b)=>{const x=d(a),y=d(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return num(z.slice(0,3).map(mod))};
 const powers=[1];for(let i=1;i<13;i++)powers.push(mul(powers[i-1],3));if(mul(powers[12],3)!==1||new Set(powers).size!==13)throw Error("T");
 const inv=x=>{if(!x)throw Error("zero inverse");return R(27).find(y=>mul(x,y)===1)};
 const slot=(j,s)=>s?neg(powers[mod13(j)]):powers[mod13(j)],mod13=x=>(x%13+13)%13;
 const template=[[0,1],[1,1],[5,0]],relation=[];for(let k=0;k<13;k++)for(const e of [1,-1])for(let f=0;f<2;f++)relation.push(template.map(([j,s])=>slot(k+e*j,s^f)));
 const unique=xs=>[...new Map(xs.map(x=>[x.join(),x])).values()];
 const permutations=x=>[[x[0],x[1],x[2]],[x[0],x[2],x[1]],[x[1],x[0],x[2]],[x[1],x[2],x[0]],[x[2],x[0],x[1]],[x[2],x[1],x[0]]];
 const unordered=unique(relation.flatMap(permutations)),ratios=[...new Set(relation.map(([a,b,c])=>mul(sub(c,a),inv(sub(b,a)))))];
 const affine=[];for(const r of ratios)for(let a=0;a<27;a++)for(let b=0;b<27;b++)if(a!==b)affine.push([a,b,add(a,mul(r,sub(b,a)))]);
 const fibres=(rel,role)=>{const m=new Map();for(const x of rel){const k=x.filter((_,j)=>j!==role).join(),v=m.get(k)||[];v.push(x[role]);m.set(k,v)}return m};
 const families={ordered:relation,unordered,affine};const facts={};for(const [n,rel] of Object.entries(families)){facts[n]={triples:rel.length,roles:R(3).map(i=>{const m=fibres(rel,i),h={};for(const v of m.values())h[v.length]=(h[v.length]||0)+1;return {pairs:m.size,histogram:h}})}}
 if(relation.length!==52||unordered.length!==312||new Set(affine.map(x=>x.join())).size!==affine.length)throw Error("relation");
 const gem=Array(27),gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"];for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
 const ordinal=[..."אבגדהוזחטיךכלםמןנסעףפץצקרשת"];
 const result={geometry:{template:relation[0],ratios:ratios.map(d),facts},charts:{}};
 for(const [name,alphabet] of Object.entries({gematria:gem,ordinal})){
  const ix=new Map(alphabet.map((x,i)=>[x,i])),seq=c=>[...c.verses.map(v=>v.letters).join("")].map(x=>ix.get(x)),blocks=(book,lo=1,hi=999)=>book.chapters.filter(c=>c.c>=lo&&c.c<=hi).flatMap(c=>{const s=seq(c);return R(Math.floor(s.length/216)).map(i=>s.slice(i*216,(i+1)*216))});
  const train=blocks(books.exodus,1,13),prior=Array(27).fill(1);for(const b of train)for(const x of b)prior[x]++;
  const total=prior.reduce((a,b)=>a+b,0);prior.forEach((v,i)=>prior[i]=v/total);
  const maps=Object.fromEntries(Object.entries(families).map(([n,r])=>[n,fibres(r,2)]));
  const arg=q=>q.indexOf(Math.max(...q)),pairs=new Map(),column=(b,j,control=false)=>[b[j],b[143-j],b[144+(control?(j+1)%72:j)]];
  for(const b of train)for(let j=0;j<72;j++){const [a,v,c]=column(b,j),k=[a,v].join(),arr=pairs.get(k)||Array(27).fill(0);arr[c]++;pairs.set(k,arr)}
  const norm=q=>{const s=q.reduce((a,b)=>a+b,0);return q.map(v=>v/s)};
  function score(bs,control=false){
   const counts=Object.fromEntries(["unigram","pair",...Object.keys(maps)].map(n=>[n,{bits:0,hits:0,eligible:0,relationHits:0,eligibleBaselineMass:0}]));let n=0;
   for(const b of bs)for(let j=19;j<72;j++){const [a,v,c]=column(b,j,control),k=[a,v].join(),pair=norm((pairs.get(k)||Array(27).fill(0)).map((x,i)=>x+10*prior[i]));n++;
    const models={unigram:prior,pair};for(const [name,map] of Object.entries(maps)){const candidates=map.get(k);models[name]=candidates?prior.map((x,i)=>.9*x+.1*(candidates.includes(i)?1/candidates.length:0)):prior;if(candidates){counts[name].eligible++;counts[name].relationHits+=candidates.includes(c);counts[name].eligibleBaselineMass+=candidates.reduce((s,i)=>s+prior[i],0)}}
    for(const [k,q] of Object.entries(models)){counts[k].bits-=Math.log2(q[c]);counts[k].hits+=arg(q)===c}
   }
   return {n,models:Object.fromEntries(Object.entries(counts).map(([k,v])=>[k,{...v,bitsPerLetter:v.bits/n}]))};
  }
  const rows=books.exodus.chapters.find(c=>c.c===14).verses.filter(v=>v.v>=19&&v.v<=21).flatMap(v=>[...v.letters].map(x=>ix.get(x)));
  result.charts[name]={alphabet:alphabet.join(""),train:score(train),shem:score([rows]),shemShift:score([rows],true),books:Object.fromEntries(Object.entries(books).map(([k,b])=>{const bs=blocks(b,k==="exodus"?16:1);return [k,{aligned:score(bs),shifted:score(bs,true)}]}))};
 }
 return result;
}
const base='Docs/support/reference/TorahCryptoCorpus20261125/';
const books=Object.fromEntries(['exodus','genesis','leviticus','numbers','deuteronomy'].map(n=>[n,JSON.parse(fs.readFileSync(base+n+'.normalized.json','utf8'))]));console.log(JSON.stringify(assay(books),null,2));
