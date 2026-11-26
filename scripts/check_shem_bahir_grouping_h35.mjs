import fs from 'node:fs';
function audit(receipt){
 const r=receipt.spans.find(x=>x.book==="exodus"&&x.ch===14).rows.map(s=>[...s]);r[1].reverse();
 const gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"],gem=Array(27);for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[t+3*((t+u)%3)+9*((t+v)%3)]=gs[i]}
 const ix=new Map(gem.map((x,i)=>[x,i])),d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],mod=x=>(x%3+3)%3,R=n=>Array.from({length:n},(_,i)=>i),num=a=>a[0]+3*a[1]+9*a[2],add=(a,b)=>num(d(a).map((x,i)=>mod(x+d(b)[i]))),neg=a=>num(d(a).map(x=>mod(-x))),sum=xs=>xs.reduce(add,0),vals=r.map(s=>s.map(x=>ix.get(x)));
 const encode=(g,h,k)=>24*g+6*h+k,decode=j=>[Math.floor(j/24),Math.floor(j%24/6),j%6];
 let roundtrips=0;for(let j=0;j<72;j++){if(encode(...decode(j))!==j)throw Error("roundtrip");roundtrips++}
 // The Bahir attests cardinalities; consecutive address assignment is ours.
 const fibres={
   groups:R(3).map(g=>R(72).filter(j=>decode(j)[0]===g)),
   directionWithinGroup:R(12).map(i=>R(72).filter(j=>Math.floor(j/6)===i)),
   sameDirection:R(4).map(h=>R(72).filter(j=>decode(j)[1]===h)),
   sameSlot:R(6).map(k=>R(72).filter(j=>decode(j)[2]===k)),
 };
 function stats(v){return Object.fromEntries(Object.entries(fibres).map(([name,bs])=>{let sums=bs.map(b=>v.map(row=>sum(b.map(j=>row[j]))));return [name,{sums,zero:sums.filter(s=>sum(s)===0).length,copiesA:sums.filter(s=>s[2]===s[0]).length,copiesB:sums.filter(s=>s[2]===s[1]).length}]}))}
 const actual=stats(vals),shift=R(72).map(s=>stats([vals[0],vals[1],vals[2].map((_,j)=>vals[2][(j+s)%72])]));
 // GF(3) matrix for selected marginal-sum constraints, one scalar coordinate at a time.
 function rank(mat){let rows=mat.map(x=>x.slice()),q=0;for(let j=0;j<72;j++){let k=q;while(k<rows.length&&!rows[k][j])k++;if(k===rows.length)continue;[rows[k],rows[q]]=[rows[q],rows[k]];let inv=rows[q][j];for(let l=j;l<72;l++)rows[q][l]=mod(rows[q][l]*inv);for(let i=q+1;i<rows.length;i++){let m=rows[i][j];for(let l=j;l<72;l++)rows[i][l]=mod(rows[i][l]-m*rows[q][l])}q++}return q}
 const constraints=Object.values(fibres).flat(),matrix=constraints.map(b=>R(72).map(j=>+b.includes(j))),allRank=rank(matrix),anchor=[0,36],withAnchors=rank(matrix.concat(anchor.map(i=>R(72).map(j=>+(i===j)))));
 const witnesses=anchor.map(j=>({column:j+1,triple:r.map(x=>x[j]).join("")}));
 const control=Object.fromEntries(Object.entries(actual).map(([name,s])=>[name,Object.fromEntries(["zero","copiesA","copiesB"].map(metric=>{const a=shift.map(x=>x[name][metric]);return [metric,{actual:s[metric],mean:a.reduce((s,x)=>s+x,0)/72,max:Math.max(...a),atLeast:a.filter(x=>x>=s[metric]).length}]}))]));
 return {roundtrips,witnesses,fibreSizes:Object.fromEntries(Object.entries(fibres).map(([n,b])=>[n,b.map(x=>x.length)])),actual,control,allRank,withAnchors,remainingWithOracleSums:27n**BigInt(72-allRank)+"",remainingWithOracleSumsAndNamedAnchors:27n**BigInt(72-withAnchors)+"",qualification:"Bahir attests grouping cardinalities, not specific numerical coordinate assignments or conservation laws. Consecutive lexicographic grouping, field chart and all tested equations are DASHI candidate assumptions. Named triples 1 and 37 from Rabbeinu Bahya commentary are disclosed target-side anchors, not predictions; oracle marginal sums use actual withheld row and measure residual only. Exact affine solution count for consistent oracle GF3 sums on unrestricted 27-state glyphs, not orthographic/linguistic count. All 72 C shifts are descriptive controls, no fresh blind validation."}
}
console.log(JSON.stringify(audit(JSON.parse(fs.readFileSync('Docs/support/reference/TorahCryptoCorpus20261125/h32-chart-independent.json','utf8'))),null,2));
