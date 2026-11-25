import fs from 'node:fs';
function audit(source,exodus,genesis){
const R=n=>Array.from({length:n},(_,i)=>i),V=R(27),mod=x=>(x%3+3)%3,d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],num=a=>a[0]+3*a[1]+9*a[2];
const add=(a,b)=>num(d(a).map((x,i)=>mod(x+d(b)[i]))),sub=(a,b)=>num(d(a).map((x,i)=>mod(x-d(b)[i])));
const mul=(a,b)=>{const x=d(a),y=d(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return num(z.slice(0,3).map(mod))};
const A=V.map(a=>V.map(b=>add(a,b))),D=V.map(a=>V.map(b=>sub(a,b))),M=V.map(a=>V.map(b=>mul(a,b))),I=V.map(x=>x?M[x].indexOf(1):0),F=V.map(x=>M[x][M[x][x]]),F2=F.map(x=>F[x]);
const gem=Array(27),gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"];for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
const ix=new Map(gem.map((x,i)=>[x,i])),enc=s=>[...s].map(c=>{if(!ix.has(c))throw Error("glyph");return ix.get(c)});
const orb=[],left=new Set(V.filter(x=>x!==0&&x!==1));while(left.size){const r=left.values().next().value,s=D[1][r],o=[...new Set([r,I[r],s,I[s],M[r][I[D[r][1]]],M[D[r][1]][I[r]]])].sort((a,b)=>a-b);for(const x of o)left.delete(x);orb.push(o)}
const orbitOf=r=>orb.findIndex(o=>o.includes(r)),frobeniusAction=orb.map(o=>[...new Set(o.map(x=>orbitOf(F[x])))]),frobeniusOrbits=[];let pending=new Set(V);while(pending.size){let x=pending.values().next().value,o=[...new Set([x,F[x],F2[x]])].sort((a,b)=>a-b);o.forEach(y=>pending.delete(y));frobeniusOrbits.push(o)}
// AGL(3,3) stabilizer of (0,1): linear invertible maps fixing e1.
// enumerate other columns, then exact orbit partition.
function span(bs){return new Set(V.filter(i=>i<3**bs.length).map(i=>bs.reduce((v,b,j)=>A[v][M[d(i)[j]][b]],0)))}
const linear=[];for(const u of V)for(const v of V){if(span([1,u,v]).size!==27)continue;linear.push(V.map(x=>d(x).reduce((s,k,j)=>A[s][M[k][[1,u,v][j]]],0)))}
const stabilizerOrbits=[];pending=new Set(V);while(pending.size){const x=pending.values().next().value,o=[...new Set(linear.map(p=>p[x]))].sort((a,b)=>a-b);o.forEach(y=>pending.delete(y));stabilizerOrbits.push(o)}
const blocks=(book,lo,hi)=>book.chapters.filter(c=>c.c>=lo&&c.c<=hi).flatMap(c=>{const s=enc(c.verses.map(v=>v.letters).join(""));return R(Math.floor(s.length/216)).map(i=>({n:72,rows:[s.slice(i*216,i*216+72),s.slice(i*216+72,i*216+144).reverse(),s.slice(i*216+144,i*216+216)]}))});
const native=source.spans.map(w=>({book:w.book,ch:w.ch,n:w.n,rows:w.rows.map((r,i)=>i===1?enc(r).reverse():enc(r))})),shem=native.find(w=>w.book==="exodus"&&w.ch===14),nt=native.filter(w=>w.book!=="exodus"),et=native.filter(w=>w.book==="exodus"&&w.ch!==14),st=blocks(exodus,1,13),sv=blocks(exodus,16,40),cross=blocks(genesis,1,50);
function frame(v,j,kind){
 const [a,b]=v,origin=a[j],pool=[b[j]];for(let k=1;k<a.length;k++)for(const t of [j-k,j+k])if(t>=0&&t<a.length)pool.push(a[t],b[t]);
 const ds=pool.map(x=>D[x][origin]),first=ds.findIndex(x=>x!==0);if(first<0)return null;
 const u=ds[first],z=x=>M[I[u]][D[x][origin]],normalized=pool.map(z),isDegenerate=a[j]===b[j];
 if(kind==="semilinear"){
   const pivot=normalized.findIndex(x=>F[x]!==x);if(pivot<0)return null;
   const transforms=[V,F,F2],k=R(3).sort((i,j)=>transforms[i][normalized[pivot]]-transforms[j][normalized[pivot]])[0],tr=transforms[k],back=transforms[(3-k)%3];
   return {encode:x=>tr[z(x)],decode:x=>A[origin][M[u][back[x]]],key:[+isDegenerate,first,pivot,tr[normalized[pivot]]],minimal:[+isDegenerate,tr[normalized[pivot]]]};
 }
 const basis=[u],indices=[first];for(let i=0;i<ds.length&&basis.length<3;i++){if(!span(basis).has(ds[i])){basis.push(ds[i]);indices.push(i)}}if(basis.length!==3)return null;
 const decode=V.map(x=>A[origin][d(x).reduce((s,t,k)=>A[s][M[t][basis[k]]],0)]),encode=V.map(x=>decode.indexOf(x));
 if(new Set(decode).size!==27)throw Error("frame");
 return {encode:x=>encode[x],decode:x=>decode[x],key:[+isDegenerate,...indices],minimal:[+isDegenerate]};
}
function sample(bs,role,kind,shift=0){return bs.flatMap(w=>{const v=w.rows.filter((_,i)=>i!==role).map((r,i)=>i===0?r.map((_,j)=>r[(j+shift)%w.n]):r);return R(w.n).map(j=>{const f=frame(v,j,kind),c=w.rows[role][j];return {f,c,r:f?f.encode(c):null,j}})})}
const mode=a=>{let m=Math.max(...a),k=a.findIndex(x=>x===m);return {k,ties:a.filter(x=>x===m).length}};
function run(train,test,kind,role,shift=0){
 const tr=sample(train,role,kind,shift),te=sample(test,role,kind,shift),tables=new Map(),global=Array(27).fill(0),raw=Array(27).fill(0);
 for(const x of tr){raw[x.c]++;if(!x.f)continue;global[x.r]++;for(const k of ["g:"+x.f.minimal.join(),"f:"+x.f.key.join()]){const t=tables.get(k)||Array(27).fill(0);t[x.r]++;tables.set(k,t)}}
 const out={n:te.length,frames:0,correct:0,coarseCorrect:0,rawModeCorrect:0,uniqueMode:0,exactSpans:0,sheetCorrect:0,conditionalOrientationCorrect:0,degenerateCorrect:0,degenerate:0,by:{},output:""};let preds=[];
 for(const x of te){out.rawModeCorrect+=mode(raw).k===x.c;if(!x.f){preds.push(null);out.output+="?";continue}out.frames++;const keys=["f:"+x.f.key.join(),"g:"+x.f.minimal.join()],sel=keys.find(k=>tables.has(k)),t=sel?tables.get(sel):global,p=mode(t),c=x.f.decode(p.k);out.by[sel?.[0]||"global"]=(out.by[sel?.[0]||"global"]||0)+1;out.correct+=c===x.c;out.coarseCorrect+=x.f.decode(mode(global).k)===x.c;out.uniqueMode+=p.ties===1;out.degenerate+=x.f.key[0];out.degenerateCorrect+=x.f.key[0]&&c===x.c;preds.push(c);out.output+=gem[c]}
 let i=0;for(const w of test){out.exactSpans+=w.rows[role].every((x,j)=>x===preds[i+j]);i+=w.n}if(test.length!==1)delete out.output;return out
}
const results=[];for(const kind of ["semilinear","affine3"])for(let role=0;role<3;role++){const tr=sample(nt,role,kind),map=new Map();for(const x of tr){if(!x.f)continue;let k=x.f.key.join(),s=map.get(k)||new Set();s.add(x.r);map.set(k,s)}results.push({kind,role,trainingFrames:tr.filter(x=>x.f).length,trainingKeys:map.size,conflictingKeys:[...map.values()].filter(s=>s.size>1).length,maxSuccessors:Math.max(...[...map.values()].map(s=>s.size)),nativeShem:run(nt,[shem],kind,role),nativeOtherExodus:run(nt,et,kind,role),nativeShift:run(nt,[shem],kind,role,1),syntheticShem:run(st,[shem],kind,role),syntheticTest:run(st,sv,kind,role),syntheticShift:run(st,sv,kind,role,1),cross:run(st,cross,kind,role)})}
return {frobeniusAction,frobeniusOrbits,linearStabilizerOrder:linear.length,linearStabilizerOrbits:stabilizerOrbits,semilinearFixed:V.filter(x=>F[x]===x),results,qualification:"Visible-only deterministic frames, first nonzero difference then first non-F3 anchor (semilinear), or first three linearly independent differences (affine3). Full visible rows used; no hidden value in frame. Mode labels learned from separate training, not proof of uniqueness. Native 82 glyphs per role and synthetic 85 training blocks compared separately; 175 synthetic test and 338 Genesis blocks previously inspected. No fresh blind validation. Candidate frame choices not source-attested. Shift retrains on shifted first visible row."}
}
const base='Docs/support/reference/TorahCryptoCorpus20261125/';
console.log(JSON.stringify(audit(...['h32-chart-independent.json','exodus.normalized.json','genesis.normalized.json'].map(n=>JSON.parse(fs.readFileSync(base+n,'utf8')))),null,2));
