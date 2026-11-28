import fs from 'node:fs';
function audit(fixture){
 const glyphs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"], ix=new Map(glyphs.map((g,i)=>[g,i])),R=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3;
 function rankAudit(triples){
  // Every distinct collinear triple of an affine F3^3 chart satisfies a+b+c=0.
  // Chart unknown: one scalar coordinate variable per original glyph.
  const rows=triples.map(t=>{let a=Array(27).fill(0);for(const x of t)a[x]=mod(a[x]+1);return a});
  let rank=0,piv=[];for(let j=0;j<27;j++){let k=rank;while(k<rows.length&&!rows[k][j])k++;if(k===rows.length)continue;[rows[k],rows[rank]]=[rows[rank],rows[k]];let p=rows[rank];if(p[j]===2)for(let l=j;l<27;l++)p[l]=mod(2*p[l]);for(let i=0;i<rows.length;i++){if(i===rank)continue;const m=rows[i][j];if(m)for(let l=j;l<27;l++)rows[i][l]=mod(rows[i][l]-m*p[l])}piv.push(j);rank++}
  const free=R(27).filter(j=>!piv.includes(j)),basis=free.map(j=>{let a=Array(27).fill(0);a[j]=1;piv.forEach((p,i)=>a[p]=mod(-rows[i][j]));return a});
  const groups=new Map();for(let i=0;i<27;i++){let key=basis.map(v=>v[i]).join();if(!groups.has(key))groups.set(key,[]);groups.get(key).push(glyphs[i])}
  return {constraints:triples.length,rank,nullity:27-rank,forcedEqualityClasses:groups.size,nonSingletonClasses:[...groups.values()].filter(x=>x.length>1),maxPossibleDistinctGlyphImages:groups.size,bijectionExcluded:groups.size<27};
 }
 function auditWindow(w){
  const rows=w.rows.map(r=>r.words.map(w=>w.glyphs).join(""));const aligned=[...rows[0]].map((a,j)=>[a,[...rows[1]][rows[0].length-1-j],[...rows[2]][j]].map(g=>ix.get(g)));
  const distinct=aligned.filter(t=>new Set(t).size===3),twoEqual=aligned.filter(t=>new Set(t).size===2),allEqual=aligned.filter(t=>new Set(t).size===1);
  const roles=R(3).map(role=>{const m=new Map();aligned.forEach((t,j)=>{const p=t.filter((_,i)=>i!==role).join(),q=m.get(p)||new Map(),l=q.get(t[role])||[];l.push(j+1);q.set(t[role],l);m.set(p,q)});
   let max=0,loss=0,witness=[];for(const [k,q] of m){max=Math.max(max,q.size);const counts=[...q.values()].map(v=>v.length).sort((a,b)=>b-a);loss+=counts.slice(2).reduce((a,b)=>a+b,0);if(q.size>2)witness.push({pair:k.split(",").map(x=>glyphs[+x]),outputs:[...q].map(([g,cols])=>({glyph:glyphs[g],columns:cols}))})}return {role,max,minimumExcludedTwoGate:loss,witness}});
  // Weighted independent set of distinct unordered triple types, where sharing
  // an unordered pair forces the same third point in any affine F3 line chart.
  const types=new Map();distinct.forEach(t=>{const k=t.slice().sort((a,b)=>a-b).join();types.set(k,(types.get(k)||0)+1)});const verts=[...types].map(([k,w])=>({t:k.split(",").map(Number),w}));const adj=verts.map((v,i)=>verts.map((u,j)=>j!==i&&v.t.filter(x=>u.t.includes(x)).length>=2?j:-1).filter(x=>x>=0));
  let unseen=new Set(R(verts.length)),components=[],nodes=0,maximum=0;while(unseen.size){let c=[unseen.values().next().value];unseen.delete(c[0]);for(let i=0;i<c.length;i++)for(const u of adj[c[i]])if(unseen.delete(u))c.push(u);components.push(c)}
  function optimum(c){nodes++;if(nodes>2e6)throw Error("search cap");if(!c.length)return 0;const v=c.reduce((a,b)=>adj[b].filter(x=>c.includes(x)).length>adj[a].filter(x=>c.includes(x)).length?b:a);if(!adj[v].some(x=>c.includes(x)))return verts[v].w+optimum(c.filter(x=>x!==v));return Math.max(optimum(c.filter(x=>x!==v)),verts[v].w+optimum(c.filter(x=>x!==v&&!adj[v].includes(x))))}
  for(const c of components)maximum+=optimum(c);
  return {book:w.book,ch:w.ch,v:w.v,rows,n:aligned.length,distinct:distinct.length,twoEqual:twoEqual.length,allEqual:allEqual.length,roles,affineLineDistinctOnly:rankAudit(distinct),affineLineAll:rankAudit(aligned),linearHypergraph:{distinctTypes:verts.length,components:components.map(c=>c.length),searchNodes:nodes,maximumCompatibleDistinctOccurrences:maximum,minimumExcludedDistinct:distinct.length-maximum,qualification:"Necessary pair-uniqueness constraint only, not sufficient for embedding in affine F3^3. Repeated glyph triples not constrained here."}};
 }
 const spans=fixture.map(auditWindow);
 const combined=fixture.flatMap(w=>{const r=w.rows.map(x=>[...x.words.map(y=>y.glyphs).join("")]);return r[0].map((a,j)=>[a,r[1][r[0].length-1-j],r[2][j]].map(g=>ix.get(g)))});
 return {spans,combinedDistinctLine:rankAudit(combined.filter(t=>new Set(t).size===3)),combinedAllLine:rankAudit(combined),qualification:"Unknown common glyph bijection into affine GF3^3. Collinearity of 3 distinct points implies their vector sum zero in characteristic3. Linear constraints on each of three coordinates have same kernel; any forced-equal scalar signatures forbid injective vector chart. Distinct-only test exempts every repeated glyph triple; all-line test additionally imposes zero sum on all triples. Two-branch oracle bound applies to arbitrary chart-independent ordered pair-only relation with at most 2 outputs, not time/history-dependent state. Actual native verse fixtures previously disclosed, retrospective obstruction not prediction."}
}
console.log(JSON.stringify(audit(JSON.parse(fs.readFileSync('Docs/support/reference/TorahCryptoCorpus20261125/h28-native-word-fixture.json','utf8'))),null,2));
