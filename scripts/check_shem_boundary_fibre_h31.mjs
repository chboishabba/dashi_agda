import fs from 'node:fs';
function audit(fixture){
 const F=new Set([..."ךםןףץ"]),M=new Set([..."כמנפצ"]),N=17;
 const bits=n=>{const s=n.toString(2),k=Math.min(52,s.length);return s.length-k+Math.log2(parseInt(s.slice(0,k),2))};
 const pow=(n,k)=>BigInt(n)**BigInt(k);
 function count(n,k){
  // distinct glyph strings, NOT word-boundary assignments. Last glyph is final or neutral.
  // first n-1 letters: f forced boundaries, m forbidden, neutral optional.
  let dp=Array.from({length:n},()=>Array(n).fill(0n));dp[0][0]=1n;
  for(let j=0;j<n-1;j++){let next=Array.from({length:n},()=>Array(n).fill(0n));for(let f=0;f<=j;f++)for(let m=0;m<=j-f;m++){let q=dp[f][m];next[f+1][m]+=5n*q;next[f][m+1]+=5n*q;next[f][m]+=17n*q}dp=next}
  let c=0n;for(let f=0;f<n;f++)for(let m=0;m<n-f;m++)if(f<=k-1&&k-1<=n-1-m)c+=22n*dp[f][m];return c
 }
 function row(r){return r.words.flatMap(w=>[...w.glyphs].map((g,i)=>({g,start:i===0,end:i===w.glyphs.length-1})))}
 const windows=fixture.map(w=>({book:w.book,ch:w.ch,v:w.v,rows:w.rows.map(row)}));
 const train=windows.filter(w=>w.book!=="exodus");
 const test=windows.filter(w=>w.book==="exodus");
 function visible(w){let A=w.rows[0],B=w.rows[1].slice().reverse();return A.map((a,i)=>({a:a.end,as:a.start,b:B[i].start,bs:B[i].end,phase:i%3,first:i===0,last:i===A.length-1}))}
 const keys={boundary:x=>[x.a,x.b],bothEnds:x=>[x.a,x.as,x.b,x.bs],phase:x=>[x.a,x.b,x.phase]};
 const tables={};for(const [name,key] of Object.entries(keys)){const m=new Map();for(const w of train){visible(w).forEach((x,i)=>{const k=key(x).join(),v=m.get(k)||[0,0];v[+w.rows[2][i].end]++;m.set(k,v)})}tables[name]=m}
 const rule={A:x=>x.a,B:x=>x.b,and:x=>x.a&&x.b,or:x=>x.a||x.b,xor:x=>x.a!==x.b};for(const [n,k] of Object.entries(keys))rule[n]=x=>{const v=tables[n].get(k(x).join());return !!v&&v[1]>v[0]};
 function score(w){const c=w.rows[2],n=c.length,k=c.filter(x=>x.end).length,full=pow(27,n),endOnly=22n*pow(27,n-1),knownCount=count(n,k),knownMask=pow(22,n);if(!knownCount||knownCount<knownMask||knownCount>endOnly)throw Error("count bounds");
  const predictions={};for(const [name,p] of Object.entries(rule)){const mask=visible(w).map(x=>x.last||p(x));let correct=0,fp=0,fn=0,viol=0;for(let j=0;j<n;j++){correct+=mask[j]===c[j].end;fp+=mask[j]&&!c[j].end;fn+=!mask[j]&&c[j].end;viol+=mask[j]?M.has(c[j].g):F.has(c[j].g)}predictions[name]={correct,fp,fn,violations:viol,predictedWords:mask.filter(Boolean).length,admitsTrueRow:viol===0,distinctCandidates:knownMask.toString()}}
  return {book:w.book,ch:w.ch,v:w.v,n,k,counts:{unrestricted:full.toString(),verseEndOnly:endOnly.toString(),wordCountOracle:knownCount.toString(),wordMaskOracle:knownMask.toString()},bits:{unrestricted:bits(full),verseEndOnly:bits(endOnly),wordCountOracle:bits(knownCount),wordMaskOracle:bits(knownMask)},predictions}
 }
 // Exhaustive small-n category enumeration, weighting concrete symbol multiplicity.
 let checked=0;for(let n=1;n<=6;n++)for(let k=1;k<=n;k++){let total=0n;for(let x=0;x<3**n;x++){let t=x,a=[];for(let j=0;j<n;j++){a.push(t%3);t=Math.floor(t/3)}if(a[n-1]===1)continue;let f=0,m=0;for(let j=0;j<n-1;j++){f+=a[j]===0;m+=a[j]===1}if(f<=k-1&&k-1<=n-1-m)total+=a.reduce((q,v)=>q*BigInt(v===2?17:5),1n)}if(total!==count(n,k))throw Error("enumeration");checked++}
 return {smallCountChecks:checked,trainingSpans:train.map(w=>({book:w.book,ch:w.ch,v:w.v,n:w.rows[2].length})),test:test.map(score),training:train.map(score),qualification:"Source orthography from H29 pinned WLC; final 5 and medial 5 disjoint, other 17 shared. Known target word count and full target mask are explicitly oracle side information, not original mask. Counts distinct glyph strings compatible with orthographic constraints only, not all grammatical or source-attested strings. A/B boundary rules use visible rows only; learned rules fit two non-Exodus spans; all targets reused exploratory fixtures. Last boundary imposed from known verse end. Middle reversed along with start/end roles. No target letters in candidate construction."}
}
console.log(JSON.stringify(audit(JSON.parse(fs.readFileSync('Docs/support/reference/TorahCryptoCorpus20261125/h28-native-word-fixture.json','utf8'))),null,2));
