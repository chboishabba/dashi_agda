import fs from 'node:fs';
function assay(book,beam,controls,source){
 const alphabet=[..."אבגדהוזחטיךכלםמןנסעףפץצקרשת"],K=27,R=n=>Array.from({length:n},(_,i)=>i),ix=new Map(alphabet.map((c,i)=>[c,i])),mod=x=>(x%3+3)%3;
 const gem=Array(27),gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"],num=a=>a[0]+3*a[1]+9*a[2],d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)];
 for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
 const fi=new Map(gem.map((c,i)=>[c,i])),toF=alphabet.map(c=>fi.get(c)),fromF=gem.map(c=>ix.get(c));
 const add=(a,b)=>num(d(a).map((x,i)=>mod(x+d(b)[i]))),neg=a=>num(d(a).map(x=>mod(-x))),sub=(a,b)=>add(a,neg(b));
 const mul=(a,b)=>{const x=d(a),y=d(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return num(z.slice(0,3).map(mod))};
 const rs=[22,9,15,4,19,6,14,23,26,10,17,18];
 const mask=R(K).map(a=>R(K).map(b=>a===b?null:new Set(rs.map(r=>fromF[add(toF[a],mul(r,sub(toF[b],toF[a])))]))));
 const seq=c=>[...c.verses.map(v=>v.letters).join("")].map(x=>ix.get(x)),blocks=cs=>cs.flatMap(c=>{const s=seq(c);return R(Math.floor(s.length/216)).map(i=>s.slice(i*216,(i+1)*216))});
 const train=book.chapters.filter(c=>c.c<=13),test=book.chapters.filter(c=>c.c>=16),un=Array(K).fill(1),bi=R(K).map(()=>Array(K).fill(0)),tri=R(K*K).map(()=>Array(K).fill(0));
 const norm=a=>{const z=a.reduce((s,x)=>s+x,0);return a.map(x=>x/z)};
 for(const c of train){const s=seq(c);for(let i=0;i<s.length;i++){un[s[i]]++;if(i)bi[s[i-1]][s[i]]++;if(i>1)tri[s[i-2]*K+s[i-1]][s[i]]++}}
 const prior=norm(un),bp=bi.map(a=>norm(a.map((x,i)=>x+10*prior[i]))),tp=tri.map((a,j)=>norm(a.map((x,i)=>x+10*bp[j%K][i])));
 const qAt=(b,j)=>tp[b[j-2]*K+b[j-1]].map(x=>.9*x+.1/K);
 // Only third-row prediction: avoid conflating distinct-anchor marginals with ratio signal.
 function event(b,j,shift){const c=j-144,a=b[(c+shift)%72],v=b[143-c],set=mask[a][v],q=qAt(b,j);if(!set)return {q,m:0,y:0,eligible:false};let m=0;for(const x of set)m+=q[x];return {q,m,y:+set.has(b[j]),eligible:true}}
 function fit(events){let l=-12,h=12;for(let i=0;i<60;i++){let t=(l+h)/2,w=Math.exp(t),g=events.reduce((s,e)=>s+e.y-w*e.m/(1-e.m+w*e.m),0);if(g>0)l=t;else h=t}return (l+h)/2}
 function delta(e,t){return e.eligible?(Math.log1p(Math.expm1(t)*e.m)-t*e.y)/Math.LN2:0}
 const tr=blocks(train),te=blocks(test),collect=(bs,sh)=>bs.flatMap(b=>R(72).map(i=>event(b,144+i,sh)));
 const byShift=R(72).map(sh=>{const a=collect(tr,sh),b=collect(te,sh),ae=a.filter(e=>e.eligible),be=b.filter(e=>e.eligible),t=fit(ae);return {shift:sh,logOdds:t,trainEligible:ae.length,trainHits:ae.reduce((s,e)=>s+e.y,0),trainExpected:ae.reduce((s,e)=>s+e.m,0),testEligible:be.length,testHits:be.reduce((s,e)=>s+e.y,0),testExpected:be.reduce((s,e)=>s+e.m,0),testDeltaBits:b.reduce((s,e)=>s+delta(e,t),0)}});
 const t=byShift[0].logOdds;
 const pool=new Map();for(const [name,cs] of Object.entries({...beam.output,...controls.output}))for(const c of cs){if(!pool.has(c.letters))pool.set(c.letters,{...c,origins:[]});pool.get(c.letters).origins.push(name)}
 const prefix=[...beam.prefix].map(c=>ix.get(c));
 const rows=[...pool.values()].map(c=>{const b=prefix.concat([...c.letters].map(x=>ix.get(x))),es=R(72).map(i=>event(b,144+i,0)),eligible=es.filter(e=>e.eligible),hit=eligible.reduce((s,e)=>s+e.y,0),base=c.wordCost+.25*c.charCost,geom=es.reduce((s,e)=>s+delta(e,t),0);return {text:c.text,origins:c.origins,languageCost:base,geometryDeltaBits:geom,jointCost:base+geom,eligible:eligible.length,inRelation:hit,escape:eligible.length-hit,degenerate:72-eligible.length,truthHits:c.hits}});
 const lang=rows.slice().sort((a,b)=>a.languageCost-b.languageCost),geo=rows.slice().sort((a,b)=>b.inRelation-a.inRelation||a.escape-b.escape),joint=rows.slice().sort((a,b)=>a.jointCost-b.jointCost);
 // An exact two-part enumerative code, no source law assumed: for every nondegenerate C, encode membership and rank in its branch.
 // For k hits among n eligible, use uniform count k then enumerative subset rank; degenerate letters are literal.
 const logchoose=(n,k)=>{let s=0;for(let i=1;i<=k;i++)s+=Math.log2((n-i+1)/i);return s};
 for(const row of rows){const n=row.eligible,k=row.inRelation;row.enumerativeBits=Math.log2(n+1)+logchoose(n,k)+k*Math.log2(12)+(n-k)*Math.log2(15)+row.degenerate*Math.log2(27);row.literalBits=72*Math.log2(27)}
 const sb=source.charts.gematria,realN=72-sb.degenerate,realK=sb.twelveHits;
 const realCode=Math.log2(realN+1)+logchoose(realN,realK)+realK*Math.log2(12)+(realN-realK)*Math.log2(15)+sb.degenerate*Math.log2(27);
 const allRanks=byShift.slice(1).map(x=>x.testDeltaBits);
 return {trainingBlocks:tr.length,testBlocks:te.length,letters:te.length*72,baseline:"character trigram with fixed 10% uniform smoothing; training-only log odds tilt; exact normalized q times weight divided by partition",byShift,alignedRank:1+allRanks.filter(x=>x<byShift[0].testDeltaBits).length,poolSize:rows.length,languageTop:lang[0],jointTop:joint[0],geometryHitTop:geo[0],languageTopJointRank:joint.indexOf(lang[0])+1,languageTopGeometryRank:geo.indexOf(lang[0])+1,rows,sourceCode:{eligible:realN,hits:realK,escape:realN-realK,degenerate:sb.degenerate,enumerativeBits:realCode,literalBits:72*Math.log2(27),qualification:"ideal real-valued bit cost conditional on first two rows and shared chart; excludes chart/model overhead; not a byte-level code"},qualification:"existing exploratory corpus, candidate pool generated with linguistic prior, no independent semantic interpretation or exhaustive search; scores conditional on earlier true letters for corpus only"};
}
const base='Docs/support/reference/TorahCryptoCorpus20261125/';
console.log(JSON.stringify(assay(...['exodus.normalized.json','h20-legible-word-decoder.json','h20-legible-word-controls.json','h20-source-role-residual.json'].map(n=>JSON.parse(fs.readFileSync(base+n,'utf8')))),null,2));
