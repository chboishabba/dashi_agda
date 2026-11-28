import fs from 'node:fs';
function audit(books){
const R=n=>Array.from({length:n},(_,i)=>i),V=R(27),mod=x=>(x%3+3)%3,d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],num=a=>a[0]+3*a[1]+9*a[2],A=V.map(a=>V.map(b=>num(d(a).map((x,i)=>mod(x+d(b)[i]))))),D=V.map(a=>V.map(b=>num(d(a).map((x,i)=>mod(x-d(b)[i])))));
const glyphs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"],ix=new Map(glyphs.map((g,i)=>[g,i])),enc=s=>[...s].map(g=>{if(!ix.has(g))throw Error("glyph");return ix.get(g)}),str=s=>s.map(x=>glyphs[x]).join("");
const seq=ch=>enc(ch.verses.map(v=>v.letters).join("")),chapters=Object.entries(books).flatMap(([book,b])=>b.chapters.map(ch=>({book,ch:ch.c,s:seq(ch)}))),ex=chapters.filter(x=>x.book==="exodus"),deut=chapters.filter(x=>x.book==="deuteronomy"),train=ex.filter(x=>x.ch<=13),prior=chapters.filter(x=>x.book!=="deuteronomy");
const old=V.map(i=>{let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);return num([t,mod(t+u),mod(t+v)])}),ayak=V.map(i=>num([(i%9+1)%3,mod(Math.floor(i%9/3)-1),mod(Math.floor(i/9)-1)])),shuffled=ayak.slice();let seed=0x44369;for(let i=26;i>0;i--){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;let j=(seed>>>0)%(i+1);[shuffled[i],shuffled[j]]=[shuffled[j],shuffled[i]]}
const charts={old,ayak,shuffled},masks=V.map(x=>d(x).reduce((s,v,i)=>s+(v?1<<i:0),0)),sign=V.map(x=>d(x).filter(v=>v).reduce((s,v,i)=>s+((v===2?1:0)<<i),0)),pop=R(8).map(m=>R(3).filter(i=>m>>i&1).length);
function unmask(m,s){let k=0;return num(R(3).map(i=>m>>i&1?1+(s>>k++&1):0))}
for(const c of Object.values(charts)){if(new Set(c).size!==27)throw Error("chart");for(const x of V)if(unmask(masks[x],sign[x])!==x)throw Error("fibre")}
const norm=a=>{let t=a.reduce((s,v)=>s+v,0);return a.map(x=>x/t)},argmax=a=>a.indexOf(Math.max(...a)),inc=(t,k,x)=>{let a=t.get(k);if(!a)t.set(k,a=Array(27).fill(0));a[x]++},blend=(a,p,k)=>a?norm(a.map((v,i)=>v+k*p[i])):p;
function fit(rows,c,shift=0){
let uni=Array(27).fill(1),bi=new Map(),tri=new Map(),r=[new Map(),new Map(),new Map()],direct=[new Map(),new Map(),new Map()];
for(const {s} of rows)for(let j=0;j<s.length;j++){let x=s[j];uni[x]++;if(j)inc(bi,s[j-1],x);if(j>1)inc(tri,27*s[j-2]+s[j-1],x);if(j>=216&&j+216+shift<s.length){let a=c[s[j-216+shift]],b=c[s[j+216+shift]],m=masks[D[b][a]],z=D[c[x]][a];inc(r[0],0,z);inc(r[1],m,z);inc(r[2],27*m+a,z);inc(direct[0],0,x);inc(direct[1],m,x);inc(direct[2],27*m+a,x)}}
let p=norm(uni),q=R(27).map(x=>blend(bi.get(x),p,10)),T=R(729).map(k=>blend(tri.get(k),q[k%27],10)),U=Array(27).fill(1/27);
function geom(left,right,n,j,kind){
 // physical index j in gap, left and right lag216 +/- shift, both observed for n<=91.
 let a0=left[left.length+j-216+shift],b0=right[j+216+shift-n];if(a0===undefined||b0===undefined)throw Error("anchor unavailable");
 let a=c[a0],b=c[b0],m=masks[D[b][a]],key=27*m+a;
 if(kind==="direct"){let z=blend(direct[0].get(0),U,27);z=blend(direct[1].get(m),z,30);return blend(direct[2].get(key),z,30)}
 let z=blend(r[0].get(0),U,27);z=blend(r[1].get(m),z,30);z=blend(r[2].get(key),z,30);
 let mp=R(8).map(m=>z.reduce((s,v,i)=>s+(masks[i]===m?v:0),0)),sp=R(8).map(m=>norm(R(2**pop[m]).map(k=>z[unmask(m,k)]+.002)));
 return V.map(x=>{let e=D[c[x]][a],m=masks[e];return mp[m]*sp[m][sign[e]]})
}
return {T,p,geom,chart:c,shift}}
function terminal(T,right,k){let v=1,a=k;for(const x of right.slice(0,2)){v*=T[a][x];a=(a%27)*27+x}return v}
function factors(f,left,right,n,mode){let arr=[];for(let j=0;j<n;j++){let g=mode==="language"||mode==="uniform"?null:f.geom(left,right,n,j,mode==="direct"?"direct":"geometry");let t=mode==="geometry"?R(729).map(()=>g):mode==="language"?f.T:R(729).map(k=>f.T[k].map((q,x)=>.8*q+.2*(g?g[x]:1/27)));arr.push(t)}return arr}
function solve(f,left,right,n,mode,check=false){
 const T=f.T,ts=factors(f,left,right,n,mode),start=27*left.at(-2)+left.at(-1);
 // Exact max-product and sum-product backward messages, no beam.
 let max=Float64Array.from(R(729).map(k=>terminal(T,right,k))),sum=max.slice(),paths=Array(n),sums=Array(n+1);sums[n]=sum;
 for(let j=n-1;j>=0;j--){let M=new Float64Array(729),S=new Float64Array(729),P=new Uint8Array(729),t=ts[j];for(let k=0;k<729;k++){let base=(k%27)*27,best=-1,a=0;for(let x=0;x<27;x++){let w=t[k][x],v=w*max[base+x];S[k]+=w*sum[base+x];if(v>best){best=v;a=x}}M[k]=best;P[k]=a}paths[j]=P;sums[j]=S;max=M;sum=S}
 let k=start,path=[];for(let j=0;j<n;j++){let x=paths[j][k];path.push(x);k=(k%27)*27+x}
 let forward=new Float64Array(729);forward[start]=1;let marginal=[],posterior=[];
 for(let j=0;j<n;j++){let next=new Float64Array(729),p=Array(27).fill(0),t=ts[j];for(let k=0;k<729;k++){let base=(k%27)*27,w=forward[k];if(!w)continue;for(let x=0;x<27;x++){let v=w*t[k][x];next[base+x]+=v;p[x]+=v*sums[j+1][base+x]}}let q=norm(p);marginal.push(argmax(q));posterior.push(Math.max(...q));forward=next}
 let Z=sum[start],P=max[start];if(!Number.isFinite(Z)||Z<=0||P>Z*(1+1e-10))throw Error("mass");
 if(check){let z=0,best=0;function recurse(k,j,w){if(j===n){w*=terminal(T,right,k);z+=w;best=Math.max(best,w);return}for(const x of V)recurse((k%27)*27+x,j+1,w*ts[j][k][x])}recurse(start,0,1);if(Math.abs(z/Z-1)>1e-10||Math.abs(best/P-1)>1e-10)throw Error("enumeration")}
 return {path,marginal,posterior,logEvidence:Math.log2(Z),mapProbability:P/Z}
}
const hits=(a,b)=>a.filter((x,i)=>x===b[i]).length;
const left=ex.find(x=>x.ch===14).s.slice(-432),target=ex.find(x=>x.ch===15).s.slice(0,91),right=ex.find(x=>x.ch===15).s.slice(91,523);if(target.length!==91||right.length<217)throw Error("original");
const configs=[["language","old",0],["uniform","old",0],["geometry","old",0],["joint","old",0],["direct","old",0],["geometry","ayak",0],["joint","ayak",0],["geometry","shuffled",0],["geometry","ayak",1]];
const original=[],regression=[],small=[];let exhaustive=0;
const windows=deut.filter(x=>x.ch%3===1&&x.s.length>=432+91+432).map(x=>({ch:x.ch,left:x.s.slice(0,432),target:x.s.slice(432,523),right:x.s.slice(523,955)}));
for(const [mode,name,shift] of configs){let f=fit(train,charts[name],shift),o=solve(f,left,right,91,mode);original.push({mode,chart:name,shift,map:hits(o.path,target),marginal:hits(o.marginal,target),mapText:str(o.path),marginalText:str(o.marginal),posteriorMean:o.posterior.reduce((s,x)=>s+x,0)/91,mapProbability:o.mapProbability});let q=fit(prior,charts[name],shift),m=0,p=0,exact=0;for(const w of windows){let z=solve(q,w.left,w.right,91,mode);m+=hits(z.path,w.target);p+=hits(z.marginal,w.target);exact+=hits(z.path,w.target)===91}regression.push({mode,chart:name,shift,spans:windows.length,n:windows.length*91,map:m,marginal:p,exact});
 for(const n of [0,1,2]){solve(q,left,right,n,mode,true);exhaustive++}
 // shorter exact masked cases, with both sides throughout.
 let stats={};for(const n of [1,3,9]){let a=0,b=0,e=0;for(const w of windows){let r=w.target.slice(n).concat(w.right),z=solve(q,w.left,r,n,mode);a+=hits(z.path,w.target.slice(0,n));b+=hits(z.marginal,w.target.slice(0,n));e+=hits(z.path,w.target.slice(0,n))===n}stats[n]={n:windows.length*n,map:a,marginal:b,exact:e}}small.push({mode,chart:name,shift,stats})
}
 // Exact source correspondence lookup: training-only, literal two-flank match; source occurrence kept.
 function retrieve(rows,l,r,n,k){let a=l.slice(-k).join(","),b=r.slice(0,k).join(","),results=[];for(const w of rows)for(let j=k;j+n+k<=w.s.length;j++){if(w.s[j-1]!==l.at(-1)||w.s[j+n]!==r[0])continue;if(w.s.slice(j-k,j).join(",")===a&&w.s.slice(j+n,j+n+k).join(",")===b)results.push({book:w.book,ch:w.ch,offset:j,text:str(w.s.slice(j,j+n))})}return results}
 const retrieval=R(3).map(i=>{let k=[3,6,12][i],r=retrieve(train,left,right,91,k);return{k,count:r.length,distinct:new Set(r.map(x=>x.text)).size,examples:r.slice(0,5)}});
 // Known seam length classification via exact marginal evidence, uniform length prior on 0..3.
 const gap=[];for(const [mode,name,shift] of [["language","old",0],["joint","ayak",0],["geometry","ayak",0]]){let f=fit(prior,charts[name],shift),matrix=R(4).map(()=>Array(4).fill(0)),located=0,locations=0;for(const w of windows)for(let n=0;n<=3;n++){let r=w.target.slice(n).concat(w.right),e=R(4).map(k=>solve(f,w.left,r,k,mode).logEvidence),guess=argmax(e);matrix[n][guess]++;if(n===1){ // true seam among 3 possible observed indices, compare evidence gain to no deletion at each
 let obs=w.left.concat(r),center=w.left.length,scores=[-1,0,1].map(delta=>{let j=center+delta,l=obs.slice(0,j),r=obs.slice(j),a=solve(f,l,r,1,mode).logEvidence,b=solve(f,l,r,0,mode).logEvidence;return a-b});located+=argmax(scores)===1;locations++}}
 gap.push({mode,chart:name,matrix,located,locations})}
 // end-of-book pseudo-end backtests with strictly earlier books: one-sided forward only;
 // no invented right boundary or target residual. Language vs exact lag transport.
 const ends=[];for(let bi=1;bi<5;bi++){const b=Object.keys(books)[bi],rows=chapters.filter(w=>w.book===b),earlier=chapters.filter(w=>Object.keys(books).indexOf(w.book)<bi),full=rows.flatMap(w=>w.s),t=full.slice(-91),l=full.slice(-523,-91),f=fit(earlier,ayak),y=l.slice();for(let j=0;j<91;j++)y.push(argmax(f.T[27*y.at(-2)+y.at(-1)]));const copy=l.slice(l.length-216,l.length-216+91);ends.push({book:b,language:hits(y.slice(-91),t),lag216:hits(copy,t),n:91})}
return{original,regression,small,windows:windows.map(x=>x.ch),exhaustive,retrieval,gap,ends,qualification:"Exact finite max/sum-product for specified positive conditional model with fixed observed +/-216 anchors and right first2 glyph likelihood. Geometry support/sign residual uses H43 arithmetic and H44-style backoff; direct shares same anchor/mask information. Right anchors participate at every position, backward messages include immediate right boundary. MAP exact up to floating arithmetic, not unique historical recovery; marginal modes not necessarily joint MAP. Original adds 432 right glyphs and 432 left glyphs (explicit extra information), target never in fit. Deut systematic chapter sample previously inspected. Length test 0..3 uniform length prior, location test only ±1 seam for synthetic single deletion; not real lacuna. Literal retrieval from training only, not cipher proof. End backtests earlier books only, lag216 zero innovation and greedy trigram, not extrapolated historical text. No compression objective."}}

const base='Docs/support/reference/TorahCryptoCorpus20261125/';const names=['genesis','exodus','leviticus','numbers','deuteronomy'];console.log(JSON.stringify(audit(Object.fromEntries(names.map(n=>[n,JSON.parse(fs.readFileSync(base+n+'.normalized.json','utf8'))])))),null,2));
