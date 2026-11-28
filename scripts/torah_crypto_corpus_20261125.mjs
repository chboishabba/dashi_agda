// Written (ketiv) projection; qere remains in pinned raw XML, not merged with written stream.
function parseBook(xml){
 const chapters=[],anomalies=[];let qCount=0,kCount=0,roundtrips=0;
 for(const [,n,raw] of xml.matchAll(/<c\b[^>]*\bn="(\d+)"[^>]*>([\s\S]*?)<\/c>/g)){
  const c=+n,by=new Map();
  for(const [fragment,v] of raw.matchAll(/<v\b[^>]*\bn="(\d+)"[^>]*>[\s\S]*?<\/v>/g)){
   const tokens=[...fragment.matchAll(/<(w|k|q)>([\s\S]*?)<\/\1>/g)].map(([_,tag,raw],id)=>({tag,raw,id}));
   qCount+=tokens.filter(x=>x.tag==="q").length;kCount+=tokens.filter(x=>x.tag==="k").length;
   if(!by.has(+v))by.set(+v,[]);
   by.get(+v).push({fragment,tokens:tokens.filter(x=>x.tag!=="q")});
  }
  const verses=[];
  for(const [v,ss] of by){
   let chars=[],slots=0,conflicts=0;
   for(let j=0;j<Math.max(...ss.map(s=>s.tokens.length));j++){
    const active=ss.map((s,i)=>({i,t:s.tokens[j]})).filter(x=>x.t&&x.t.raw!==".");
    if(active.length!==1){anomalies.push({chapter:c,verse:v,slot:j,active:active.length});if(active.length===0)continue;conflicts++}
    for(const {i,t} of active){slots++;for(const [offset,glyph] of [...t.raw].entries())if(/[\u05d0-\u05ea]/u.test(glyph)){if([...ss[i].tokens[j].raw][offset]!==glyph)throw Error("source");chars.push(glyph);roundtrips++}}
   }
   verses.push({v,letters:chars.join(""),slots,conflicts});
  }
  chapters.push({c,verses});
 }
 return {chapters,anomalies,qCount,kCount,roundtrips};
}
function summarize(book){
 const all=book.chapters.flatMap(c=>c.verses.map(v=>({...v,c:c.c}))),windows=[];
 for(const c of book.chapters)for(let i=0;i<c.verses.length-2;i++){
  const v=c.verses.slice(i,i+3);if(v.some(x=>x.conflicts)||v[1].v!==v[0].v+1||v[2].v!==v[1].v+1)continue;
  const lengths=v.map(x=>x.letters.length);windows.push({c:c.c,start:v[0].v,lengths,equal:lengths.every(x=>x===lengths[0])});
 }
 return {chapters:book.chapters.length,verses:all.length,letters:all.reduce((s,v)=>s+v.letters.length,0),sourceRoundtrips:book.roundtrips,ketiv:book.kCount,qere:book.qCount,anomalyCount:book.anomalies.length,conflicts:all.filter(v=>v.conflicts).map(v=>[v.c,v.v]),eligibleWindows:windows.length,equalWindows:windows.filter(w=>w.equal),exact72:windows.filter(w=>w.lengths.every(x=>x===72)),chapterCounts:book.chapters.map(c=>({c:c.c,verses:c.verses.length,letters:c.verses.reduce((s,v)=>s+v.letters.length,0)}))};
}
export {parseBook,summarize};
