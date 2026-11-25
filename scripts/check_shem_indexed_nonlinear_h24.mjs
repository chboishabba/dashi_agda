import fs from 'node:fs';
function audit(exodus,genesis,source){
 const R=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3,d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],num=a=>a[0]+3*a[1]+9*a[2];
 const add=(a,b)=>num(d(a).map((x,i)=>mod(x+d(b)[i]))),sub=(a,b)=>num(d(a).map((x,i)=>mod(x-d(b)[i])));
 const mul=(a,b)=>{const x=d(a),y=d(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return num(z.slice(0,3).map(mod))};
 const A=R(27).map(a=>R(27).map(b=>add(a,b))),D=R(27).map(a=>R(27).map(b=>sub(a,b))),M=R(27).map(a=>R(27).map(b=>mul(a,b))),I=R(27).map(x=>x?M[x].indexOf(1):0);
 const gem=Array(27),gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"];for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
 const ix=new Map(gem.map((x,i)=>[x,i])),enc=s=>[...s].map(x=>{if(!ix.has(x))throw Error("glyph");return ix.get(x)});
 const blocks=(book,name,lo,hi)=>book.chapters.filter(c=>c.c>=lo&&c.c<=hi).flatMap(c=>{const s=enc(c.verses.map(v=>v.letters).join(""));return R(Math.floor(s.length/216)).map(i=>({name,chapter:c.c,block:i,rows:[s.slice(i*216,i*216+72),s.slice(i*216+72,i*216+144).reverse(),s.slice(i*216+144,i*216+216)]}))});
 const train=blocks(exodus,"exodus",1,13),test=blocks(exodus,"exodus",16,40),cross=blocks(genesis,"genesis",1,50);
 const shem={name:"shem",chapter:14,block:0,rows:[enc(source.sourceRows[0]),enc(source.sourceRows[1]).reverse(),enc(source.sourceRows[2])]};
 // Decoder receives only first two rows; no hidden C is read by frame or inference.
 function frame(rows,j,shift=0){
  const u=rows[0],v=rows[1],at=(row,k)=>row[(k+72)%72],a=at(u,j+shift),b=at(v,j),around=[at(u,j-1+shift),at(v,j-1),at(u,j+1+shift),at(v,j+1),at(u,j-2+shift),at(v,j-2),at(u,j+2+shift),at(v,j+2)];
  const pool=[b,...around],k=pool.findIndex(x=>x!==a);if(k<0)return null;
  const scale=D[pool[k]][a],norm=x=>M[I[scale]][D[x][a]];
  return {a,scale,anchorIndex:k,z:[norm(b),...around.map(norm)],phase:j%4,boundary:j===0?0:j===71?2:1};
 }
 const restore=(f,r)=>A[f.a][M[f.scale][r]];
 const label=(f,c)=>M[I[f.scale]][D[c][f.a]];
 const sample=(bs,shift=0)=>bs.flatMap(b=>R(72).map(j=>{const f=frame(b.rows,j,shift);return {f,j,y:b.rows[2][j],r:f?label(f,b.rows[2][j]):null,where:[b.name,b.chapter,b.block,j]}}));
 const keys={
  pair:f=>[f.anchorIndex,f.z[0]],
  oneNeighbour:f=>[f.anchorIndex,f.z[0],f.z[1]],
  twoNeighbour:f=>[f.anchorIndex,...f.z.slice(0,3)],
  local:f=>[f.anchorIndex,...f.z.slice(0,5)],
  wider:f=>[f.anchorIndex,...f.z],
  indexedLocal:f=>[f.anchorIndex,f.phase,f.boundary,...f.z.slice(0,5)]
 };
 const fit=(rows,key)=>{const m=new Map();for(const x of rows){if(!x.f)continue;const k=key(x.f).join(",");if(!m.has(k))m.set(k,Array(27).fill(0));m.get(k)[x.r]++}return m};
 const top=a=>{let best=-1,n=0,which=-1;for(let i=0;i<a.length;i++){if(a[i]>best){best=a[i];n=1;which=i}else if(a[i]===best)n++}return n===1?which:null};
 const training=sample(train),testing=sample(test),crossing=sample(cross),target=sample([shem]);let models={};
 function stats(rows,key,m){let seen=0,unique=0,correct=0,truthInFibre=0,ambiguous=0,unseen=0;const out=[];for(const x of rows){const c=x.f?m.get(key(x.f).join(",")):null;if(!c){unseen++;out.push("?");continue}seen++;const supp=c.filter(n=>n>0).length;truthInFibre+=c[x.r]>0;ambiguous+=supp>1;const p=top(c);if(p===null){out.push("?");continue}unique++;const y=restore(x.f,p);correct+=y===x.y;out.push(gem[y]);}return {n:rows.length,seen,unique,correct,truthInFibre,ambiguous,unseen,output:rows.length===72?out.join(""):undefined}}
 for(const [name,key] of Object.entries(keys)){const m=fit(training,key);let conflicts=0,oracle=0;for(const a of m.values()){conflicts+=a.filter(x=>x>0).length>1;oracle+=Math.max(...a)}models[name]={trainingKeys:m.size,trainingConflicts:conflicts,trainingOracleCorrect:oracle,test:stats(testing,key,m),cross:stats(crossing,key,m),shem:stats(target,key,m)}}
 // Backoff from independently visible, normalized indexed local context to less specific context.
 const order=["indexedLocal","local","twoNeighbour","oneNeighbour","pair"];
 function backoff(trainRows,testRows){const tables=order.map(k=>fit(trainRows,keys[k]));const global=Array(27).fill(0);for(const x of trainRows)if(x.f)global[x.r]++;let hits=0,unique=0,seen=0;const by={},out=[];let exactBlocks=0,blockHits=0;for(const x of testRows){let p=null,used="none";if(x.f){for(let i=0;i<order.length;i++){const c=tables[i].get(keys[order[i]](x.f).join(","));if(c&&top(c)!==null){p=top(c);used=order[i];break}}if(p===null){p=top(global);used="global";}}if(p!==null){unique++;if(used!=="global")seen++;const y=restore(x.f,p);hits+=y===x.y;blockHits+=y===x.y;out.push(gem[y])}else out.push("?");by[used]=(by[used]||0)+1;if(out.length%72===0){exactBlocks+=blockHits===72;blockHits=0}}
 return {n:testRows.length,hits,unique,seen,by,exactBlocks,output:testRows.length===72?out.join(""):undefined}}
 const backoffResult={test:backoff(training,testing),cross:backoff(training,crossing),shem:backoff(training,target),shiftedTest:backoff(sample(train,1),sample(test,1)),shiftedShem:backoff(sample(train,1),sample([shem],1))};
 // Exact polynomial consistency over normalized local visible coordinates, with target only on RHS.
 // Restrict to ordinary local pair frame and use four neighbour coordinates; shared degree<=3 map.
 const monomials=(n,deg)=>{const out=[[]];function visit(start,left,path){if(!left){out.push(path);return}for(let j=start;j<n;j++)visit(j,left-1,path.concat(j))}for(let k=1;k<=deg;k++)visit(0,k,[]);return out};
 const eligible=training.filter(x=>x.f&&x.f.anchorIndex===0);
 function poly(deg){const terms=monomials(4,deg),n=terms.length,mat=eligible.map(x=>[...terms.map(t=>t.reduce((a,j)=>M[a][x.f.z[j+1]],1)),x.r]);let rank=0;for(let j=0;j<n;j++){let k=rank;while(k<mat.length&&!mat[k][j])k++;if(k===mat.length)continue;[mat[k],mat[rank]]=[mat[rank],mat[k]];const p=mat[rank],z=I[p[j]];for(let c=j;c<=n;c++)p[c]=M[p[c]][z];for(let i=rank+1;i<mat.length;i++){const f=mat[i][j];if(f)for(let c=j;c<=n;c++)mat[i][c]=D[mat[i][c]][M[f][p[c]]]}rank++}return {degree:deg,features:n,rank,augmentedRank:rank+Number(mat.slice(rank).some(row=>row[n]!==0)),consistent:!mat.slice(rank).some(row=>row[n]!==0),trainingRows:eligible.length}}
 // Frame chart covariance checks over all 702 affine actors for representative visible stencil,
 // not a claim of actual Torah equivariance.
 const b=shem.rows,j=1,f=frame(b,j),checks={normalization:0,reconstruction:0};for(let a=0;a<27;a++)for(let u=1;u<27;u++){const tr=x=>A[a][M[u][x]],m=frame(b.slice(0,2).map(row=>row.map(tr)),j);if(m.z.join()!==f.z.join()||m.anchorIndex!==f.anchorIndex)throw Error("covariance");checks.normalization++;for(let r=0;r<27;r++){if(restore(m,r)!==tr(restore(f,r)))throw Error("rebuild");checks.reconstruction++}}
 return {trainingBlocks:train.length,testBlocks:test.length,crossBlocks:cross.length,frame:"anchor visible A; scale first nonzero visible difference from B, then cyclic adjacent A/B; preserve fallback index, scale, zero and signs",models,backoff:backoffResult,poly:[1,2,3].map(poly),checks,actualShem:shem.rows[2].map(x=>gem[x]).join(""),qualification:"exploratory reused corpus; empirical normalized context maps fitted on Exodus 1–13 only, no linguistic model, no C supplied to inference. A unique modal value is not logically unique support. Shift retrained. Cyclic wrap is candidate boundary convention, not source-attested. Genesis previously inspected and not a fresh blind holdout."}
}
const base='Docs/support/reference/TorahCryptoCorpus20261125/';
console.log(JSON.stringify(audit(...['exodus.normalized.json','genesis.normalized.json','h20-source-role-residual.json'].map(n=>JSON.parse(fs.readFileSync(base+n,'utf8')))),null,2));
