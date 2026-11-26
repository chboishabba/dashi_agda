import fs from 'node:fs';
function audit(book,source,genesis,native){
 const R=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3,d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],num=a=>a[0]+3*a[1]+9*a[2];
 const add=(a,b)=>num(d(a).map((x,i)=>mod(x+d(b)[i]))),sub=(a,b)=>num(d(a).map((x,i)=>mod(x-d(b)[i])));
 const mul=(a,b)=>{const x=d(a),y=d(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return num(z.slice(0,3).map(mod))};
 const A=R(27).map(a=>R(27).map(b=>add(a,b))),D=R(27).map(a=>R(27).map(b=>sub(a,b))),M=R(27).map(a=>R(27).map(b=>mul(a,b))),I=R(27).map(x=>x?M[x].indexOf(1):0),all=R(27);
 const gem=Array(27),gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"];for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
 const ix=new Map(gem.map((x,i)=>[x,i])),enc=s=>[...s].map(c=>{if(!ix.has(c))throw Error("glyph");return ix.get(c)});
 const blocks=(lo,hi)=>book.chapters.filter(c=>c.c>=lo&&c.c<=hi).flatMap(c=>{const s=enc(c.verses.map(v=>v.letters).join(""));return R(Math.floor(s.length/216)).map(i=>({rows:[s.slice(i*216,i*216+72),s.slice(i*216+72,i*216+144).reverse(),s.slice(i*216+144,i*216+216)]}))});
 const target={rows:[enc(source.sourceRows[0]),enc(source.sourceRows[1]).reverse(),enc(source.sourceRows[2])]},train=blocks(1,13),test=blocks(16,40);
 function frames(v){const [a,b]=v;return R(72).map(j=>{const pool=[b[j],a[j-1],b[j-1],a[j+1],b[j+1],a[j-2],b[j-2],a[j+2],b[j+2]],k=pool.findIndex(x=>x!==undefined&&x!==a[j]);return k<0?null:{a:a[j],u:D[pool[k]][a[j]],k}})}
 const z=(f,x)=>M[I[f.u]][D[x][f.a]],restore=(f,r)=>A[f.a][M[f.u][r]],compose=(q,p)=>p.map(x=>q[x]),inverse=p=>all.map(x=>p.indexOf(x));
 const map=(f,g,kind)=>all.map(r=>kind==="normalized"?r:kind==="physical"?z(g,restore(f,r)):A[r][z(g,f.a)]);

 const cross=genesis.chapters.flatMap(c=>{const s=enc(c.verses.map(v=>v.letters).join(""));return R(Math.floor(s.length/216)).map(i=>({rows:[s.slice(i*216,i*216+72),s.slice(i*216+72,i*216+144).reverse(),s.slice(i*216+144,i*216+216)]}))});
 const glyphs=s=>s.map(x=>gem[x]).join(""),mask=x=>d(x).reduce((s,v,i)=>s+(v?1<<i:0),0),pop=x=>d(x).filter(Boolean).length;
 function select(v,n,sel){if(sel==="13"||sel==="27")return n>=+sel?n-(+sel):-1;for(let p=n-1;p>=0;p--)if(v[0][p]===v[0][n]&&(sel==="A"||v[1][p]===v[1][n]))return p;return -1}

 const pow=[1];for(let j=1;j<=13;j++)pow.push(M[pow.at(-1)][3]);if(pow[13]!==1||new Set(pow.slice(0,13)).size!==13)throw Error("order13");
 const group=[];for(let k=0;k<13;k++)for(const s of [1,2])for(const e of [0,1])group.push({k,s,e,T:all.map(x=>M[M[s][pow[k]]][e?I[x]:x])});
 const affine=[];for(let a=1;a<27;a++)for(let b=0;b<27;b++)affine.push({a,b,T:all.map(x=>A[M[a][x]][b])});
 const key=g=>g.T.join(","),idx=new Map(group.map((g,i)=>[key(g),i]));let closure=0;for(const g of group){if(g.T[0]!==0||new Set(g.T).size!==27)throw Error("R13");for(const h of group){if(!idx.has(compose(g.T,h.T).join(",")))throw Error("closure");closure++}}
 function collect(ws,sel,kind,shift=0){let E=[],stats={blocks:0,zero:0,nonzero:0,mixed:0,firstZero:0,firstNonzero:0,seedOrbitCeiling:0,firstCrossings:0};for(const w of ws){let v=w.rows.slice(0,2),fs=frames(v);if(fs.some(x=>!x))continue;let r=w.rows[2].map((_,j)=>z(fs[j],w.rows[2][(j+shift)%72]));let zeros=r.filter(x=>x===0).length;stats.blocks++;stats.zero+=zeros;stats.nonzero+=72-zeros;stats.mixed+=zeros>0&&zeros<72;stats.firstZero+=r[0]===0;stats.firstNonzero+=r[0]!==0;stats.seedOrbitCeiling+=r.slice(1).filter(x=>!!x===!!r[0]).length;stats.firstCrossings+=r.some(x=>!!x!==!!r[0]);for(let n=1;n<72;n++){let p=select(v,n,sel),a=kind==="physical"?z(fs[n],restore(fs[n-1],r[n-1])):r[n-1],b=p<0?-1:kind==="physical"?z(fs[n],restore(fs[p],r[p])):r[p];E.push([a,b,r[n]])}}return{E,stats}}
 // M/F are both maps in current normalized fibre; F is inverse of the earlier-port return.
 // Score every pair exactly via marginal coverage minus simultaneous coverage.
 function optimize(E,G){const N=G.length,W=Math.ceil(E.length/32),ma=Array.from({length:N},()=>new Uint32Array(W)),fa=Array.from({length:N},()=>new Uint32Array(W)),mc=new Uint32Array(N),fc=new Uint32Array(N);
 for(let j=0;j<E.length;j++){const [a,b,y]=E[j];for(let k=0;k<N;k++){if(G[k].T[a]===y){ma[k][j>>>5]|=1<<(j&31);mc[k]++}if(b>=0&&G[k].T[b]===y){fa[k][j>>>5]|=1<<(j&31);fc[k]++}}}
 const pc=x=>{x-=(x>>>1)&0x55555555;x=(x&0x33333333)+((x>>>2)&0x33333333);return (((x+(x>>>4))&0x0f0f0f0f)*0x01010101)>>>24};
 let best=-1,pair=[0,0],ties=0;for(let a=0;a<N;a++)for(let b=0;b<N;b++){let n=mc[a]+fc[b];if(n<best)continue;for(let j=0;j<W;j++)n-=pc(ma[a][j]&fa[b][j]);if(n>best){best=n;pair=[a,b];ties=1}else if(n===best)ties++}return{best,pair,ties,pairs:N*N}}
 function score(E,G,pair){let hits=0,unique=0,uniqueTrue=0,minWeight=0,hist=[0,0,0,0],forcedZeroCross=0;for(const [a,b,y] of E){let m=G[pair[0]].T[a],f=b<0?m:G[pair[1]].T[b];let ok=m===y||f===y;hits+=ok;unique+=m===f;uniqueTrue+=m===f&&ok;let w=Math.min(pop(D[y][m]),pop(D[y][f]));hist[w]++;minWeight+=w;forcedZeroCross+=(!!a!==!!y&&(b<0||!!b!==!!y))}return{n:E.length,hits,unique,uniqueTrue,minWeight,hist,forcedZeroCross}}
 const results=[];for(const sel of ["A","pair","13","27"])for(const kind of ["normalized","physical"]){const tr=collect(train,sel,kind),te=collect(test,sel,kind),cr=collect(cross,sel,kind),sh=collect(test,sel,kind,1),shem=collect([target],sel,kind);
 const fit=optimize(tr.E,group),oracle=optimize(shem.E,group),affineOracle=optimize(shem.E,affine);
 results.push({sel,kind,fit:{...fit,m:group[fit.pair[0]],f:group[fit.pair[1]]},shemOracle:{...oracle,score:score(shem.E,group,oracle.pair)},affineOracle:{...affineOracle,score:score(shem.E,affine,affineOracle.pair)},frozenShem:score(shem.E,group,fit.pair),test:score(te.E,group,fit.pair),cross:score(cr.E,group,fit.pair),shift:score(sh.E,group,fit.pair),orbitStats:{shem:shem.stats,test:te.stats,cross:cr.stats}})}
 // Verify minimum support-weight residual for any signed R13 transport of an input.
 let orbit=[];for(const a of all)for(const y of all){let w=Math.min(...group.map(g=>pop(D[y][g.T[a]])));let expect=!a?pop(y):!y?1:0;if(w!==expect)throw Error("orbit bound");orbit.push(w)}
 return {groupSize:group.length,closure,affineSize:affine.length,orbitChecks:orbit.length,results,qualification:"H47 source transcription only: no numerical creator M/F rule recovered. Exact exhaustive fixed pair of 52 signed R13 permutations for M and inverse-F, normalized or physical current-frame transport, four visible earlier-index selectors. Train chooses pair maximizing hindsight gate union on Ex1-13, deterministic first tie; heldout oracle gate coverage generous, not free prediction. Shem retrospective optimum separately, plus enlarged 702 affine field maps pair hindsight upper bound only (not full arbitrary affine GF3^3). Score minimum residual support among selected M/F candidates with true predecessors and hindsight gate, not independent residual. Fixed zero in normalized chart gives seed-orbit obstruction only for normalized transports (physical rechart may move zero); stats reported both but not claimed for physical. No source table, no fresh blind."}
}

const base='Docs/support/reference/TorahCryptoCorpus20261125/';console.log(JSON.stringify(audit(...['exodus.normalized.json','h20-source-role-residual.json','genesis.normalized.json','h32-chart-independent.json'].map(n=>JSON.parse(fs.readFileSync(base+n,'utf8')))),null,2));
