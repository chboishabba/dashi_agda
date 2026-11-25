import fs from 'node:fs';
function audit(books){
 const gem=Array(27),gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"],mod=x=>(x%3+3)%3,d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],num=a=>a[0]+3*a[1]+9*a[2],R=n=>Array.from({length:n},(_,i)=>i);
 for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
 const ix=new Map(gem.map((x,i)=>[x,i]));
 const blocks=(book,name,lo=1,hi=999)=>book.chapters.filter(c=>c.c>=lo&&c.c<=hi).flatMap(c=>{const s=[...c.verses.map(v=>v.letters).join("")].map(x=>ix.get(x));return R(Math.floor(s.length/216)).map(i=>({book:name,chapter:c.c,block:i,s:s.slice(i*216,(i+1)*216)}))});
 const train=Object.entries(books).flatMap(([name,b])=>blocks(b,name,1,name==="exodus"?13:999)),test=blocks(books.exodus,"exodus",16,40);
 const mat=train.map(({s})=>Uint8Array.from([1,...s.flatMap(d)])),n=433,total=649;
 let rank=0;for(let j=0;j<n;j++){let k=rank;while(k<mat.length&&!mat[k][j])k++;if(k===mat.length)continue;[mat[k],mat[rank]]=[mat[rank],mat[k]];const p=mat[rank],v=p[j];if(v===2)for(let c=j;c<total;c++)p[c]=p[c]===0?0:3-p[c];
 for(let i=rank+1;i<mat.length;i++){const row=mat[i],f=row[j];if(f)for(let c=j;c<total;c++)row[c]=(row[c]+6-f*p[c])%3}rank++}
 const bad=R(216).map(j=>mat.slice(rank).some(row=>row[n+j]!==0));
 const positions=R(72).map(j=>{const pairs=new Map();for(const b of test){const a=b.s[j],v=b.s[143-j],c=b.s[144+j],k=a*27+v;if(!pairs.has(k))pairs.set(k,new Map());const m=pairs.get(k);m.set(c,(m.get(c)||0)+1)}let ceiling=0,collisions=0;for(const m of pairs.values()){ceiling+=Math.max(...m.values());collisions+=m.size>1}return {column:j,ceiling,collisions}});
 return {trainBlocks:train.length,trainByBook:Object.fromEntries(Object.keys(books).map(n=>[n,train.filter(b=>b.book===n).length])),predictorRank:rank,predictorColumns:n,outputTritCoordinates:216,inconsistentTritCoordinates:bad.filter(Boolean).length,inconsistentGlyphColumns:R(72).filter(j=>bad.slice(3*j,3*j+3).some(Boolean)).length,indexedPairOnly:{testBlocks:test.length,letters:test.length*72,oracleMaxCorrect:positions.reduce((s,x)=>s+x.ceiling,0),columnsWithCollision:positions.filter(x=>x.collisions).length,positions},qualification:"fixed affine GF3 map from all 432 input trit coordinates to all 216 output trit coordinates; allows arbitrary cross-coordinate mixing including Frobenius, but not nonlinear or block-dependent actions. Indexed pair ceiling only adds column, not chapter or surrounding text. Existing exploratory corpus and synthetic chapter blocks; not fresh blind validation."}
}
const base='Docs/support/reference/TorahCryptoCorpus20261125/';
console.log(JSON.stringify(audit(Object.fromEntries(['exodus','genesis','leviticus','numbers','deuteronomy'].map(n=>[n,JSON.parse(fs.readFileSync(base+n+'.normalized.json','utf8'))]))),null,2));
