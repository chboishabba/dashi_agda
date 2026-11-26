import fs from 'node:fs';
function audit(fixture){
const w=fixture.find(x=>x.book==="exodus"&&x.ch===14),rows=w.rows.map(r=>r.words.flatMap(w=>[...w.glyphs].map((g,i)=>({g,end:i===w.glyphs.length-1}))));rows[1].reverse();
const V=Array.from({length:27},(_,i)=>i),R=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3,d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],num=a=>a[0]+3*a[1]+9*a[2],add=(a,b)=>num(d(a).map((x,i)=>mod(x+d(b)[i]))),sub=(a,b)=>num(d(a).map((x,i)=>mod(x-d(b)[i])));
const A=V.map(a=>V.map(b=>add(a,b))),D=V.map(a=>V.map(b=>sub(a,b))),mul=(a,b)=>{const x=d(a),y=d(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return num(z.slice(0,3).map(mod))};
const M=V.map(a=>V.map(b=>mul(a,b))),I=V.map(a=>a?M[a].indexOf(1):0),gem=Array(27),gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"];for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
const ix=new Map(gem.map((x,i)=>[x,i])),vals=rows.map(row=>row.map(x=>ix.get(x.g))),[a,b,c]=vals,final=new Set([..."ךםןףץ"]),medial=new Set([..."כמנפצ"]),orbits=[],pending=new Set(V.filter(x=>x>1));
while(pending.size){const r=pending.values().next().value,s=D[1][r],o=[...new Set([r,I[r],s,I[s],M[r][I[D[r][1]]],M[D[r][1]][I[r]]])];o.forEach(x=>pending.delete(x));orbits.push(o)}
const sheet=(a,b,c)=>a===b?(a===c?"allEqual":"equalAnchors"):c===a?"first":c===b?"second":"orbit"+orbits.findIndex(o=>o.includes(M[D[c][a]][I[D[b][a]]]));
const domains=R(72).map(j=>V.filter(x=>(j!==0&&j!==36||x===c[j])&&(rows[2][j].end?!medial.has(gem[x]):!final.has(gem[x]))&&sheet(a[j],b[j],x)===sheet(a[j],b[j],c[j])));
const j=(g,h,k)=>24*g+6*h+k,sum=xs=>xs.reduce((s,x)=>A[s][x],0),mix=(x,g,h,k)=>A[D[D[x[j(g,h,k)]][x[j(g,h+1,k)]]][x[j(g,h,k+1)]]][x[j(g,h+1,k+1)]];
const cells=R(3).flatMap(g=>R(3).flatMap(h=>R(5).map(k=>[g,h,k]))),ms=vals.map(x=>cells.map(p=>mix(x,...p)));
const score=(x,y,z)=>({zero:z.filter((v,i)=>sum([v,x[i],y[i]])===0).length,copyA:z.filter((v,i)=>v===x[i]).length,copyB:z.filter((v,i)=>v===y[i]).length,zeroC:z.filter(v=>v===0).length});
const actual=score(...ms),controls=R(72).map(s=>score(ms[0],ms[1],cells.map(p=>mix(c.map((_,i)=>c[(i+s)%72]),...p))));
const control=Object.fromEntries(Object.keys(actual).map(k=>[k,{actual:actual[k],mean:controls.reduce((s,x)=>s+x[k],0)/72,max:Math.max(...controls.map(x=>x[k])),atLeast:controls.filter(x=>x[k]>=actual[k]).length}]));
// Oracle mixed differences imply d(g,h,k)=u_h+v_k, u_0=0. True row sums require sum_k v_k=0 (6u=0).
const group=[];for(let g=0;g<3;g++){let out=[],tested=0,validU=0;for(const u1 of V)for(const u2 of V)for(const u3 of V){tested++;const u=[0,u1,u2,u3],choices=R(6).map(k=>V.filter(v=>R(4).every(h=>domains[j(g,h,k)].includes(A[c[j(g,h,k)]][A[u[h]][v]]))));if(choices.some(x=>!x.length))continue;validU++;
const walk=(vs,s)=>{if(vs.length===6){if(s!==0)return;const sig=vs.map(v=>A[sum(u)][v]); // 4v=v in characteristic3
const delta=R(24).map(i=>A[u[Math.floor(i/6)]][vs[i%6]]);out.push({sig,delta});return;}for(const v of choices[vs.length])walk(vs.concat(v),A[s][v]);};walk([],0);}
group.push({g,tested,validU,solutions:out});}
// Common-slot sums require sig0+sig1+sig2=0. Count exact distinct delta arrays, no trace multiplicity.
const map=new Map();for(const x of group[2].solutions){const k=x.sig.join();if(!map.has(k))map.set(k,[]);map.get(k).push(x)}
let count=0n,witnesses=[],pairChecks=0;for(const x of group[0].solutions)for(const y of group[1].solutions){pairChecks++;const key=x.sig.map((v,i)=>D[0][A[v][y.sig[i]]]).join(),zs=map.get(key)||[];count+=BigInt(zs.length);for(const z of zs.slice(0,Math.max(0,4-witnesses.length))){const delta=x.delta.concat(y.delta,z.delta),alt=c.map((v,i)=>A[v][delta[i]]);if(alt.some((v,i)=>!domains[i].includes(v))||cells.some(p=>mix(alt,...p)!==mix(c,...p)))throw Error("invalid witness");for(let g=0;g<3;g++)for(let h=0;h<4;h++)if(sum(R(6).map(k=>delta[j(g,h,k)]))!==0)throw Error("row");for(let k=0;k<6;k++)if(sum(R(3).flatMap(g=>R(4).map(h=>delta[j(g,h,k)])))!==0)throw Error("slot");witnesses.push({changed:R(72).filter(i=>delta[i]!==0).map(i=>i+1),output:alt.map(v=>gem[v]).join("")})}}
return {actual,control,mixedCount:45,domainSizes:domains.map(x=>x.length),group:group.map(x=>({g:x.g,tested:x.tested,validU:x.validU,solutions:x.solutions.length})),pairChecks,exactCombinedOracleCount:count.toString(),witnesses,qualification:"True mixed differences, true H35 marginal sums, true sheet, true word mask and named anchors are target-side ORACLE information. Exact count of compatible glyph strings under these constraints alone, not blind recovery or grammatical alternatives. Mixed differences on consecutive candidate Bahir addresses are DASHI hypotheses. Shift controls descriptive; source geometry not claimed to provide equations."}
}
console.log(JSON.stringify(audit(JSON.parse(fs.readFileSync('Docs/support/reference/TorahCryptoCorpus20261125/h28-native-word-fixture.json','utf8'))),null,2));
