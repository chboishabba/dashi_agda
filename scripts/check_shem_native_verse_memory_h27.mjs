import fs from 'node:fs';
function audit(books){
 const R=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3,d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],num=a=>a[0]+3*a[1]+9*a[2];
 const add=(a,b)=>num(d(a).map((x,i)=>mod(x+d(b)[i]))),sub=(a,b)=>num(d(a).map((x,i)=>mod(x-d(b)[i])));
 const mul=(a,b)=>{const x=d(a),y=d(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return num(z.slice(0,3).map(mod))};
 const all=R(27),A=all.map(a=>all.map(b=>add(a,b))),D=all.map(a=>all.map(b=>sub(a,b))),M=all.map(a=>all.map(b=>mul(a,b))),I=all.map(x=>x?M[x].indexOf(1):0);
 const gem=Array(27),gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"];for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
 const ix=new Map(gem.map((x,i)=>[x,i])),enc=s=>[...s].map(c=>{if(!ix.has(c))throw Error("glyph");return ix.get(c)});
 // Native verse boundaries only; no chapter block padding, no length adjustment.
 function extract(book,name){const out=[];for(const ch of book.chapters)for(let k=0;k+2<ch.verses.length;k++){const vs=ch.verses.slice(k,k+3),rows=vs.map(v=>enc(v.letters));if(vs.some(v=>v.conflicts)||vs[1].v!==vs[0].v+1||vs[2].v!==vs[1].v+1||rows[0].length<3||rows.some(r=>r.length!==rows[0].length))continue;rows[1].reverse();out.push({book:name,c:ch.c,v:vs.map(v=>v.v),rows})}return out}
 const by=Object.fromEntries(Object.entries(books).map(([n,b])=>[n,extract(b,n)])),train=Object.entries(by).filter(([n])=>n!=="exodus").flatMap(([,v])=>v),test=by.exodus.filter(b=>!(b.c===14&&b.v[0]===19)),shem=by.exodus.find(b=>b.c===14&&b.v[0]===19);if(!shem)throw Error("missing Shem");
 const frame=(v,j)=>{const [a,b]=v,pool=[b[j],a[j-1],b[j-1],a[j+1],b[j+1],...a,...b],k=pool.findIndex(x=>x!==undefined&&x!==a[j]);return k<0?null:{a:a[j],u:D[pool[k]][a[j]],k}};
 const z=(f,x)=>M[I[f.u]][D[x][f.a]],restore=(f,r)=>A[f.a][M[f.u][r]];
 // Causal memory addressed by already observed A or ordered A/B; source j
 // never aliases old occurrence time p. Visible rows available in full.
 function features(v,selector,shift=0){const a=v[0],b=v[1],n=a.length,vis=[a.map((_,j)=>a[(j+shift)%n]),b],mem=new Map(),out=[];for(let j=0;j<n;j++){const f=frame(vis,j),key=selector==="pair"?vis[0][j]+","+b[j]:String(vis[0][j]),p=mem.get(key)??null;mem.set(key,j);out.push({f,p,j,b:f?z(f,b[j]):null,edge:j===0||j===n-1?1:0})}return out}
 const mode=c=>{let k=0;for(let i=1;i<27;i++)if(c[i]>c[k])k=i;return k},count=()=>Array(27).fill(0);
 function fit(bs,selector,kind,shift=0){const tables=new Map(),global=count(),reset=count(),unigram=count(),innov=count();let returns=0;
  function put(k,x){if(!tables.has(k))tables.set(k,count());tables.get(k)[x]++}
  for(const b of bs){const ff=features(b.rows.slice(0,2),selector,shift),c=b.rows[2],r=ff.map((f,j)=>f.f?z(f.f,c[j]):null);for(let j=0;j<c.length;j++){unigram[c[j]]++;const f=ff[j];if(!f.f)continue;global[r[j]]++;if(f.p===null||r[f.p]===null){reset[r[j]]++;put("reset:"+f.b,r[j]);continue}
   returns++;const prev=kind==="physical"?z(f.f,c[f.p]):r[f.p],delta=D[r[j]][prev];innov[delta]++;put("d:"+f.b,delta);put("d:"+f.b+":"+(j-f.p)%3,delta);put("d:"+f.b+":"+(j-f.p)%3+":"+prev,delta)
  }}return {tables,global,reset,unigram,innov,returns}}
 function predict(b,model,selector,kind,shift=0,oracle=false){const ff=features(b.rows.slice(0,2),selector,shift),out=[],rs=[],c=b.rows[2];let returns=0,hitsReturn=0,zeroInnov=0;for(let j=0;j<c.length;j++){const f=ff[j];let y;
   if(kind==="unigram"||!f.f)y=mode(model.unigram);
   else if(kind==="static")y=restore(f.f,mode(model.global));
   else if(f.p===null||rs[f.p]===null){y=restore(f.f,mode(model.tables.get("reset:"+f.b)||model.reset))}
   else{returns++;const prev=kind==="physical"?z(f.f,oracle?c[f.p]:out[f.p]):oracle?z(ff[f.p].f,c[f.p]):rs[f.p],k="d:"+f.b+":"+(j-f.p)%3,tab=model.tables.get(k+":"+prev)||model.tables.get(k)||model.tables.get("d:"+f.b)||model.innov,delta=mode(tab);zeroInnov+=delta===0;y=restore(f.f,A[prev][delta]);hitsReturn+=y===c[j]}
   out.push(y);rs.push(f.f?z(f.f,y):null);
  }return {hits:out.filter((y,j)=>y===c[j]).length,n:c.length,returns,hitsReturn,zeroInnov,exact:out.every((y,j)=>y===c[j]),output:out.map(x=>gem[x]).join("")}}
 function summarize(bs,model,selector,kind,shift=0,oracle=false){const r={n:0,hits:0,spans:bs.length,exact:0,returns:0,hitsReturn:0};for(const b of bs){const s=predict(b,model,selector,kind,shift,oracle);for(const k of ["n","hits","returns","hitsReturn"])r[k]+=s[k];r.exact+=s.exact}return r}
 const variants=[];for(const selector of ["a","pair"])for(const kind of ["normalized","physical","static","unigram"]){const m=fit(train,selector,kind);const shift=fit(train,selector,kind,1);variants.push({selector,kind,trainingReturns:m.returns,exodus:summarize(test,m,selector,kind),shem:predict(shem,m,selector,kind),oracleExodus:summarize(test,m,selector,kind,0,true),oracleShem:predict(shem,m,selector,kind,0,true),shiftExodus:summarize(test,shift,selector,kind,1),shiftShem:predict(shem,shift,selector,kind,1)})}
 // exact capacity required for any deterministic return update of specified state.
 // At a return use true previous r only for this training diagnostic.
 const capacity={};for(const selector of ["a","pair"])for(const kind of ["normalized","physical"]){const maps=[new Map(),new Map(),new Map()];let edges=0;for(const b of train){const ff=features(b.rows.slice(0,2),selector),c=b.rows[2];for(let j=0;j<c.length;j++){const f=ff[j];if(f.p===null||!f.f||!ff[f.p].f)continue;edges++;const prev=kind==="physical"?z(f.f,c[f.p]):z(ff[f.p].f,c[f.p]),r=z(f.f,c[j]),keys=[[prev],[prev,f.b],[prev,f.b,(j-f.p)%3]];for(let k=0;k<3;k++){const key=keys[k].join(",");if(!maps[k].has(key))maps[k].set(key,new Set());maps[k].get(key).add(r)}}}
 capacity[selector+":"+kind]={edges,levels:maps.map(m=>({keys:m.size,conflicts:[...m.values()].filter(s=>s.size>1).length,maxSuccessors:Math.max(0,...[...m.values()].map(s=>s.size))}))}}
 return {byBook:Object.fromEntries(Object.entries(by).map(([n,bs])=>[n,{spans:bs.length,glyphs:bs.reduce((s,b)=>s+b.rows[0].length,0),locations:bs.map(b=>({chapter:b.c,verses:b.v,length:b.rows[0].length}))}])),trainingSpans:train.length,testSpans:test.length,actualShem:shem.rows[2].map(x=>gem[x]).join(""),variants,capacity,qualification:"Actual consecutive equal-length verse triples within same chapter, raw WLC normalized glyphs, middle reverse, length>=3 and zero parser conflicts. Other four books train, Exodus test (Shem separately). Previously inspected corpus, not fresh blind validation. Overlapping verse triples possible. Candidate observed-memory keys and update law not creator-attested. Inference stores only own predictions; oracle prior true glyph separately marked; static and unigram baselines; shifted A retrained control; ties lowest field code. No target glyph used in ordinary inference."}
}
const base='Docs/support/reference/TorahCryptoCorpus20261125/';
console.log(JSON.stringify(audit(Object.fromEntries(['genesis','exodus','leviticus','numbers','deuteronomy'].map(n=>[n,JSON.parse(fs.readFileSync(base+n+'.normalized.json','utf8'))]))),null,2));
