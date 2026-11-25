import fs from 'node:fs';
function audit(source,exodus,genesis){
 const R=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3,d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],num=a=>a[0]+3*a[1]+9*a[2];
 const add=(a,b)=>num(d(a).map((x,i)=>mod(x+d(b)[i]))),neg=a=>num(d(a).map(x=>mod(-x))),sub=(a,b)=>add(a,neg(b));
 const mul=(a,b)=>{const x=d(a),y=d(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return num(z.slice(0,3).map(mod))};
 const A=R(27).map(a=>R(27).map(b=>add(a,b))),D=R(27).map(a=>R(27).map(b=>sub(a,b))),M=R(27).map(a=>R(27).map(b=>mul(a,b))),I=R(27).map(x=>x?M[x].indexOf(1):0);
 const gem=Array(27),gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"];for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
 const ix=new Map(gem.map((c,i)=>[c,i])),g=x=>gem[x],to=s=>[...s].map(c=>{if(!ix.has(c))throw Error("glyph");return ix.get(c)});
 const rs=[22,14],rs12=[22,9,15,4,19,6,14,23,26,10,17,18];
 const all=R(27),complete=(r,a,b)=>A[a][M[r][D[b][a]]];
 function candidates(pair,role,ratios){
  const [u,v]=pair;if(u===v)return [];
  return [...new Set(ratios.map(r=>role===2?complete(r,u,v):role===1?A[u][M[I[r]][D[v][u]]]:M[I[D[1][r]]][D[v][M[r][u]]]))].sort((a,b)=>a-b)
 }
 const blocks=(book,name,lo,hi)=>book.chapters.filter(c=>c.c>=lo&&c.c<=hi).flatMap(c=>{const s=to(c.verses.map(v=>v.letters).join(""));return R(Math.floor(s.length/216)).map(i=>({book:name,chapter:c.c,block:i,seq:s.slice(i*216,i*216+216)}))});
 const cols=b=>R(72).map(j=>({values:[b.seq[j],b.seq[143-j],b.seq[144+j]],where:{book:b.book,chapter:b.chapter,block:b.block,column:j}}));
 const shem=source.shemTriplets.map((s,j)=>({values:to(s),where:{book:"exodus",chapter:14,verses:[19,20,21],column:j}}));
 const tr=blocks(exodus,"exodus",1,13),te=blocks(exodus,"exodus",16,40),gen=blocks(genesis,"genesis",1,50);
 function assay(records,role){
  const pairs=new Map(),byRule={};for(const [name,rr] of Object.entries({direct:[22],reflected:[14],two:rs,twelve:rs12})){let hits=0,unique=0,correctUnique=0,empty=0;const histogram={};for(const r of records){const pair=r.values.filter((_,i)=>i!==role),c=candidates(pair,role,rr);hits+=c.includes(r.values[role]);unique+=c.length===1;correctUnique+=c.length===1&&c[0]===r.values[role];empty+=!c.length;histogram[c.length]=(histogram[c.length]||0)+1}byRule[name]={truthInFibre:hits,unique,correctUnique,empty,histogram}}
  for(const r of records){const p=r.values.filter((_,i)=>i!==role),key=p.join(),v=r.values[role];if(!pairs.has(key))pairs.set(key,new Map());const m=pairs.get(key);if(!m.has(v))m.set(v,{count:0,where:r.where});m.get(v).count++}
  let ambiguous=0,ambiguousOccurrences=0,ceiling=0,largest=0,witness=null;
  for(const [k,m] of pairs){const entries=[...m.entries()];ceiling+=Math.max(...entries.map(([,v])=>v.count));largest=Math.max(largest,m.size);if(m.size>1){ambiguous++;ambiguousOccurrences+=entries.reduce((s,[,v])=>s+v.count,0);if(!witness)witness={pair:k.split(",").map(x=>g(+x)),outputs:entries.slice(0,2).map(([x,v])=>({glyph:g(x),...v}))}}}
  return {n:records.length,byRule,pairOnly:{distinctPairs:pairs.size,ambiguousPairs:ambiguous,ambiguousOccurrences,oracleMaxCorrect:ceiling,largestObservedFibre:largest,witness,qualification:"in-sample oracle ceiling for any deterministic function of ordered visible glyph pair only; not a learned decoder; excludes position/context"}}
 }
 const shemRoles=R(3).map(r=>assay(shem,r)),trainRoles=R(3).map(r=>assay(tr.flatMap(cols),r)),testRoles=R(3).map(r=>assay(te.flatMap(cols),r));
 // Stronger family: any fixed affine map over GF27 from *all* 144 visible letters to all 72 outputs.
 // Row reduction on actual chapter blocks; no target of Shem or Exodus15 participates.
 // Carry all 72 RHS columns through elimination; zero predictor row with nonzero RHS refutes exact fit.
 const trainAll=tr.concat(gen),n=145,out=72,mat=trainAll.map(b=>[1,...b.seq.slice(0,144),...b.seq.slice(144)]);
 let rank=0;for(let j=0;j<n;j++){let k=rank;while(k<mat.length&&!mat[k][j])k++;if(k===mat.length)continue;[mat[k],mat[rank]]=[mat[rank],mat[k]];const p=mat[rank],z=I[p[j]];for(let c=j;c<n+out;c++)p[c]=M[p[c]][z];for(let i=rank+1;i<mat.length;i++){const f=mat[i][j];if(f)for(let c=j;c<n+out;c++)mat[i][c]=D[mat[i][c]][M[f][p[c]]]}rank++}
 const inconsistent=R(out).map(j=>mat.slice(rank).some(row=>row[n+j]!==0));
 // Exact constraints on the disclosed 91-mask: 53 known A,B pairs, 19 missing B,C pairs.
 const s=to(exodus.chapters.find(c=>c.c===14).verses.map(v=>v.letters).join("")).slice(1728);if(s.length!==125)throw Error("prefix");
 const known=R(53).map(j=>[s[j+19],s[143-(j+19)]]),distinct=known.filter(([a,b])=>a!==b).length;
 const mask={knownPairs:53,distinctKnownPairs:distinct,equalKnownPairs:53-distinct,doubleMissingColumns:19,strictTwoSolutions:distinct===53?"2^53 * 52^19":"0",strictTwelveSolutions:distinct===53?"12^53 * 312^19":"0",allEscapeSolutions:"27^91",qualification:"strict distinct-anchor models; missing B has 26 possibilities, C has 2 or12; zero if any known equal pair. Full escape allows all assignments."};
 return {source:"pinned WLC / H20 exact indexed Shem",chart:"existing H18b gematria",shemRoles,trainRoles,testRoles,affineFullRows:{trainingBlocks:trainAll.length,exodusBlocks:tr.length,genesisBlocks:gen.length,predictorColumns:n,predictorRank:rank,inconsistentOutputColumns:inconsistent.filter(Boolean).length,outputColumns:out,qualification:"fixed affine GF27 map on 144 input glyphs; not arbitrary nonlinear or indexed/context-dependent geometry; corpus blocks synthetic not true verse triplets"},mask,qualification:"previously inspected regression corpus; no fresh blind holdout or recovered text"}
}
const base='Docs/support/reference/TorahCryptoCorpus20261125/';
console.log(JSON.stringify(audit(...['h20-source-role-residual.json','exodus.normalized.json','genesis.normalized.json'].map(n=>JSON.parse(fs.readFileSync(base+n,'utf8')))),null,2));
