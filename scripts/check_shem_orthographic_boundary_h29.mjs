import fs from 'node:fs';
function audit(raw,fixtures){
 const R=n=>Array.from({length:n},(_,i)=>i),med="כמנפצ",fin="ךםןףץ",gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"],fold=x=>fin.includes(x)?med[fin.indexOf(x)]:x,allowed=(x,end)=>end?!med.includes(x):!fin.includes(x);
 const corpus={};for(const [name,xml] of Object.entries(raw)){
  let words=0,glyphs=0,exceptions=[],endCounts={final:0,medial:0,other:0},internalCounts={final:0,medial:0,other:0},holes=0,conflicts=0;
  for(const [,cn,ch] of xml.matchAll(/<c\b[^>]*\bn="(\d+)"[^>]*>([\s\S]*?)<\/c>/g)){
   const by=new Map();for(const [v,vn] of ch.matchAll(/<v\b[^>]*\bn="(\d+)"[^>]*>[\s\S]*?<\/v>/g)){if(!by.has(vn))by.set(vn,[]);by.get(vn).push([...v.matchAll(/<(w|k|q)>([\s\S]*?)<\/\1>/g)].map(m=>({tag:m[1],raw:m[2]})).filter(x=>x.tag!=="q"))}
   for(const [vn,ss] of by)for(let j=0;j<Math.max(...ss.map(x=>x.length));j++){
    const a=ss.map((s,i)=>({i,t:s[j]})).filter(x=>x.t&&x.t.raw!==".");if(!a.length){holes++;continue}if(a.length!==1){conflicts++;continue}
    const w=[...a[0].t.raw].filter(x=>gs.includes(x));if(!w.length)continue;words++;glyphs+=w.length;for(let i=0;i<w.length;i++){const e=i===w.length-1,x=w[i],type=fin.includes(x)?"final":med.includes(x)?"medial":"other";(e?endCounts:internalCounts)[type]++;if(!allowed(x,e))exceptions.push({chapter:+cn,verse:+vn,slot:j,segment:a[0].i,offset:i,word:w.join(""),glyph:x,end:e})}
   }
  }
  corpus[name]={words,glyphs,holes,conflicts,endCounts,internalCounts,exceptions};
 }
 const mod=x=>(x%3+3)%3,d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)],num=a=>a[0]+3*a[1]+9*a[2],add=(a,b)=>num(d(a).map((v,i)=>mod(v+d(b)[i]))),sub=(a,b)=>num(d(a).map((v,i)=>mod(v-d(b)[i])));
 const mul=(a,b)=>{let x=d(a),y=d(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return num(z.slice(0,3).map(mod))};
 const inv=x=>R(27).find(y=>mul(x,y)===1),ratio=(a,b,c)=>mul(sub(c,a),inv(sub(b,a))),ps=x=>[[x[0],x[1],x[2]],[x[0],x[2],x[1]],[x[1],x[0],x[2]],[x[1],x[2],x[0]],[x[2],x[0],x[1]],[x[2],x[1],x[0]]],rat=[22,14],twelve=[...new Set(rat.flatMap(r=>ps([0,1,r]).map(x=>ratio(...x))))];if(twelve.length!==12)throw Error("ratio");
 const gem=Array(27);for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
 const ix=new Map(gem.map((x,i)=>[x,i]));
 const spans=fixtures.map(f=>{const rows=f.rows.map(r=>r.words.flatMap(w=>[...w.glyphs].map((g,i)=>({g,end:i===w.glyphs.length-1,start:i===0,length:w.glyphs.length,offset:i,slot:w.slot}))));rows[1].reverse();const n=rows[0].length,roles=[];
 for(let role=0;role<3;role++){
  const configs=["pair","pairBoundary","pairAllWordOffsets","pairTargetBoundary","pairAllBoundary"].map(k=>({k,map:new Map()}));
  const stats=Object.fromEntries(["two","twelve"].map(k=>[k,{eligible:0,truth:0,truthAfter:0,emptyBefore:0,emptyAfter:0,singleBefore:0,singleAfter:0,correctSingleAfter:0,totalBefore:0,totalAfter:0}]));
  for(let j=0;j<n;j++){
   const t=rows.map(r=>r[j]),obs=t.filter((_,i)=>i!==role),y=t[role],key=obs.map(x=>x.g).join("");
   const keys=[key,key+":"+obs.map(x=>+x.end).join(""),key+":"+obs.map(x=>x.length+","+x.offset).join(";"),key+":"+ +y.end,key+":"+t.map(x=>+x.end).join("")];
   configs.forEach((c,k)=>{const m=c.map.get(keys[k])||new Map();m.set(y.g,(m.get(y.g)||0)+1);c.map.set(keys[k],m)});
   for(const [name,rs] of Object.entries({two:rat,twelve})){
    const s=stats[name],cand=[];for(const g of gs){const z=t.map((x,i)=>ix.get(i===role?g:x.g));if(new Set(z).size===3&&rs.includes(ratio(...z)))cand.push(g)}
    const filt=cand.filter(g=>allowed(g,y.end));s.eligible+=obs[0].g!==obs[1].g;s.truth+=cand.includes(y.g);s.truthAfter+=filt.includes(y.g);s.emptyBefore+=!cand.length;s.emptyAfter+=!filt.length;s.singleBefore+=cand.length===1;s.singleAfter+=filt.length===1;s.correctSingleAfter+=filt.length===1&&filt[0]===y.g;s.totalBefore+=cand.length;s.totalAfter+=filt.length;
   }
  }
  roles.push({role,orthographyViolations:rows[role].filter(x=>!allowed(x.g,x.end)).length,oracle:configs.map(({k,map})=>({k,keys:map.size,conflicts:[...map.values()].filter(x=>x.size>1).length,ceiling:[...map.values()].reduce((s,x)=>s+Math.max(...x.values()),0)})),relations:stats});
 }return {book:f.book,ch:f.ch,v:f.v,n,roles,wordCounts:rows.map(r=>r.filter(x=>x.end).length)};
 });
 return {corpus,spans,geometry:{ratio2:rat,ratio12:twelve},notes:"Word-end flag is extra observed metadata only in a separate mask, not inferred from original two visible rows. Orthography convention tested against pinned written XML token boundaries; maqqef/tokenization is source specific. Oracle ceilings use true target labels for retrospective collision diagnostic only; not trained predictive accuracy. No target glyphs supplied to relation generation; truth used for scores. Existing fixtures exploratory."};
}
const raw=Object.fromEntries(['genesis','exodus','leviticus','numbers','deuteronomy'].map(n=>[n,fs.readFileSync(process.argv[2]+'/'+n+'.xml','utf8')]));const fixtures=JSON.parse(fs.readFileSync('Docs/support/reference/TorahCryptoCorpus20261125/h28-native-word-fixture.json','utf8'));console.log(JSON.stringify(audit(raw,fixtures),null,2));
