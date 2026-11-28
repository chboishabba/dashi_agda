import fs from 'node:fs';
function audit(s){
 const fixture=JSON.parse(s.slice(s.indexOf("["),s.indexOf("];")+1)),R=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3;
 const rows=R(3).map(r=>{
  const seg=fixture.filter(s=>s.includes('n="'+(19+r)+'"')).map(s=>({label:s.match(/ s="([^"]+)"/)[1],words:[...s.matchAll(/<w>([\s\S]*?)<\/w>/g)].map(x=>x[1])}));
  const out=[];for(let j=0;j<seg[0].words.length;j++){
   const active=seg.map((s,i)=>({s,i})).filter(({s})=>s.words[j]!==".");if(active.length!==1)throw Error("partition");
   const {s,i}=active[0];for(const [offset,glyph] of [...s.words[j]].entries())if(/[\u05d0-\u05ea]/u.test(glyph))out.push({verse:r+19,segment:i,label:s.label,wordSlot:j,offset,glyph,rawLetterIndex:out.length});
  }
  if(out.length!==72)throw Error("row");return out
 });
 const gem=Array(27),gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"],num=a=>a[0]+3*a[1]+9*a[2],d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)];
 for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
 const add=(a,b)=>num(d(a).map((x,i)=>mod(x+d(b)[i]))),neg=a=>num(d(a).map(x=>mod(-x))),sub=(a,b)=>add(a,neg(b));
 const mul=(a,b)=>{const x=d(a),y=d(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return num(z.slice(0,3).map(mod))};
 const inv=x=>R(27).find(y=>mul(x,y)===1),ratio=(a,b,c)=>mul(sub(c,a),inv(sub(b,a))),two=[22,14],twelve=[22,9,15,4,19,6,14,23,26,10,17,18];
 function encode(a,b,c){let u=sub(b,a);return u?{anchor:a,difference:u,kind:"ratio",residual:ratio(a,b,c)}:{anchor:a,difference:0,kind:"degenerate",residual:sub(c,a)}}
 function decode(z){const {anchor:a,difference:u,residual:r}=z;return [a,add(a,u),add(a,u?mul(u,r):r)]}
 const columns=R(72).map(j=>[rows[0][j],rows[1][71-j],rows[2][j]]);
 if(new Set(columns.flat().map(x=>x.verse+":"+x.rawLetterIndex)).size!==216)throw Error("coverage");
 const charts={};for(const [name,alphabet] of Object.entries({gematria:gem,ordinal:[..."אבגדהוזחטיךכלםמןנסעףפץצקרשת"]})){
  const ix=new Map(alphabet.map((x,i)=>[x,i])),records=columns.map((xs,j)=>{const vs=xs.map(x=>ix.get(x.glyph)),z=encode(...vs),back=decode(z);if(vs.some((x,i)=>x!==back[i]))throw Error("inverse");
   return {column:j,occurrences:xs,values:vs,chart:z,memberTwo:z.kind==="ratio"&&two.includes(z.residual),memberTwelve:z.kind==="ratio"&&twelve.includes(z.residual)}});
  const controls=R(72).map(k=>{let twoHits=0,twelveHits=0;for(let j=0;j<72;j++){const z=encode(ix.get(rows[0][j].glyph),ix.get(rows[1][71-j].glyph),ix.get(rows[2][(j+k)%72].glyph));if(z.kind==="ratio"){twoHits+=two.includes(z.residual);twelveHits+=twelve.includes(z.residual)}}return {shift:k,twoHits,twelveHits}});
  charts[name]={degenerate:records.filter(x=>x.chart.kind==="degenerate").length,twoHits:controls[0].twoHits,twelveHits:controls[0].twelveHits,shiftControls:controls,records}
 }
 const restored=R(3).map(r=>columns.map(x=>x[r]).sort((a,b)=>a.rawLetterIndex-b.rawLetterIndex).map(x=>x.glyph).join(""));
 if(restored.some((s,r)=>s!==rows[r].map(x=>x.glyph).join("")))throw Error("source");
 return {source:"pinned WLC Exodus 14:19-21 H2 fixture",sourceRows:restored,shemTriplets:columns.map(x=>x.map(y=>y.glyph).join("")),sourceCoverage:216,chartRoundtripsPerAlphabet:72,charts,qualification:"actual source occurrences with reversible candidate coordinate charts; membership is not historical operator recognition; shifts exploratory"}
}
console.log(JSON.stringify(audit(fs.readFileSync(new URL('./check_shem216_r13_indexed_20261125.mjs',import.meta.url),'utf8')),null,2));
