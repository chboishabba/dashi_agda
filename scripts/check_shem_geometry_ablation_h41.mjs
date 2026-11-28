import fs from 'node:fs';
function assay(book,words,previous,source,genesis){
 const alphabet=[..."אבגדהוזחטיךכלםמןנסעףפץצקרשת"],K=27,ix=new Map(alphabet.map((c,i)=>[c,i])),range=n=>Array.from({length:n},(_,i)=>i),mod=x=>(x%3+3)%3;
 const gem=Array(27),gs=[..."אבגדהוזחטיכלמנסעפצקרשתךםןףץ"],num=a=>a[0]+3*a[1]+9*a[2],d=x=>[x%3,Math.floor(x/3)%3,Math.floor(x/9)];
 for(let i=0;i<27;i++){let t=Math.floor(i/9),u=i%3,v=Math.floor(i%9/3);gem[num([t,mod(t+u),mod(t+v)])]=gs[i]}
 const fieldIx=new Map(gem.map((c,i)=>[c,i])),toF=alphabet.map(c=>fieldIx.get(c)),fromF=gem.map(c=>ix.get(c));
 const add=(a,b)=>num(d(a).map((x,i)=>mod(x+d(b)[i]))),neg=a=>num(d(a).map(x=>mod(-x))),sub=(a,b)=>add(a,neg(b));
 const mul=(a,b)=>{const x=d(a),y=d(b),z=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)z[i+j]+=x[i]*y[j];for(let i=4;i>=3;i--){z[i-3]+=z[i];z[i-2]+=z[i]}return num(z.slice(0,3).map(mod))};
 const inv=x=>range(27).find(y=>mul(x,y)===1);
 const ratio=(a,b,c)=>mul(sub(c,a),inv(sub(b,a)));
 const seeds=[22,14],perms=x=>[[x[0],x[1],x[2]],[x[0],x[2],x[1]],[x[1],x[0],x[2]],[x[1],x[2],x[0]],[x[2],x[0],x[1]],[x[2],x[1],x[0]]];
 const roleRatios=[...new Set(seeds.flatMap(r=>perms([0,1,r]).map(x=>ratio(...x))))];if(roleRatios.length!==12)throw Error("role ratio");
 const charseq=c=>[...c.verses.map(v=>v.letters).join("")].map(x=>ix.get(x));
 const train=book.chapters.filter(c=>c.c<=13),prior=Array(K).fill(1),bi=range(K).map(()=>Array(K).fill(0)),tri=range(K*K).map(()=>Array(K).fill(0));
 for(const ch of train){const s=charseq(ch);for(let i=0;i<s.length;i++){prior[s[i]]++;if(i)bi[s[i-1]][s[i]]++;if(i>1)tri[s[i-2]*K+s[i-1]][s[i]]++}}
 const norm=a=>{const sum=a.reduce((s,x)=>s+x,0);return a.map(x=>x/sum)};
 const p=norm(prior),bp=bi.map(a=>norm(a.map((x,i)=>x+10*p[i]))),tp=tri.map((a,j)=>norm(a.map((x,i)=>x+10*bp[j%K][i])));
 // Conditional geometric distribution for the actual mask: B gets only A; C gets A and previously available B.
 // No hidden target value is used. Uniform distinct-anchor marginal for B.
 const makeGeometry=rs=>{
  const map=range(27).map(a=>range(27).map(b=>{if(a===b)return null;return rs.map(r=>fromF[add(toF[a],mul(r,sub(toF[b],toF[a])))])}));
  return (seq,j,shift=0)=>{
   if(j<144){const col=143-j,a=seq[(col+shift)%72];return range(K).map(x=>x===a?0:1/26)}
   const col=j-144,a=seq[(col+shift)%72],b=seq[143-col],vals=map[a][b];return vals?range(K).map(x=>vals.includes(x)?1/vals.length:0):p;
  };
 };

 const coords=range(3).flatMap(g=>range(4).flatMap(h=>range(6).map(k=>[g,h,k]))),parents=coords.map((p,i)=>coords.map((q,j)=>j!==i&&q.every((v,k)=>v===0||v===p[k])?j:-1).filter(j=>j>=0)),masks=coords.map(([g,h,k])=>+(g!==0)+2*(h!==0)+4*(k!==0));
 const A=range(27).map(a=>range(27).map(b=>add(a,b))),D=range(27).map(a=>range(27).map(b=>sub(a,b)));
 function info(s,j,shift){const role=Math.floor(j/72),k=j%72,z=[];for(let i=0;i<=k;i++){const anchor=toF[s[role===1?(71-i+shift)%72:143-(i+shift)%72]],off=parents[i].reduce((v,q)=>A[v][z[q]],anchor);if(i===k)return {role,mask:masks[k],anchor,off};z.push(D[toF[s[role*72+i]]][off])}}
 const key=(f,k)=>k===0?''+f.role:k===1?f.role+':'+f.mask:f.role+':'+f.mask+':'+f.anchor;
 const trainingBlocks=train.flatMap(c=>{const x=charseq(c);return range(Math.floor(x.length/216)).map(i=>x.slice(i*216,(i+1)*216))});
 function fit(shift){const tables=[new Map(),new Map(),new Map()];for(const s of trainingBlocks)for(let j=72;j<216;j++){const f=info(s,j,shift),z=D[toF[s[j]]][f.off];for(let k=0;k<3;k++){const id=key(f,k),t=tables[k].get(id)||Array(27).fill(0);t[z]++;tables[k].set(id,t)}}return tables}
 const fits=[fit(0),fit(1)];
 function tensor(s,j,shift=0){const f=info(s,j,shift),t=fits[shift];let z=norm(t[0].get(key(f,0)).map(v=>v+1));for(let k=1;k<3;k++){const a=t[k].get(key(f,k));if(a)z=norm(a.map((v,i)=>v+20*z[i]))}return range(27).map(i=>z[D[toF[i]][f.off]])}
 const uniform=()=>range(27).map(()=>1/27),alpha=.2;
 const models={trigram:null,uniform,tensor,shifted:tensor};
 function score(block){const counts={};for(const [name,geom] of Object.entries(models)){let bits=0,hits=0;for(let j=125;j<216;j++){const q=tp[block[j-2]*K+block[j-1]],g=geom?geom(block,j,name==="shifted"?1:0):null;const prob=g?q.map((x,i)=>(1-alpha)*x+alpha*g[i]):q;if(Math.abs(prob.reduce((s,x)=>s+x,0)-1)>1e-9)throw Error("norm");bits-=Math.log2(prob[block[j]]);hits+=prob.indexOf(Math.max(...prob))===block[j]}counts[name]={bits,hits}}return counts}
 const blocks=book.chapters.filter(c=>c.c>=16).flatMap(c=>{const x=charseq(c);return range(Math.floor(x.length/216)).map(i=>x.slice(i*216,(i+1)*216))});
 const stats=Object.fromEntries(Object.keys(models).map(n=>[n,{bits:0,hits:0}]));
 for(const block of blocks){const result=score(block);for(const n in stats){stats[n].bits+=result[n].bits;stats[n].hits+=result[n].hits}}
 for(const a of Object.values(stats)){a.bitsPerLetter=a.bits/(91*blocks.length);a.accuracy=a.hits/(91*blocks.length)}

 const prefix=charseq(book.chapters.find(c=>c.c===14)).slice(1728),truth=charseq(book.chapters.find(c=>c.c===15)).slice(0,91),encode=s=>[...s].map(c=>ix.get(c));if(prefix.map(x=>alphabet[x]).join("")!==previous.prefix||truth.map(x=>alphabet[x]).join("")!==previous.actual)throw Error("source");
 const cand=new Map([[previous.actual,{labels:["actual"]}]]);for(const [mode,cs] of Object.entries(previous.output))for(let i=0;i<cs.length;i++){const c=cs[i],r=cand.get(c.letters)||{labels:[]};r.labels.push(mode+":"+(i+1));cand.set(c.letters,r)}
 for(const [s,r] of cand){const suf=encode(s),full=prefix.concat(suf);let lang=0,g=0,sh=0,joint=0,uni=0,shiftJoint=0;for(let j=125;j<216;j++){let x=full[j],q=tp[full[j-2]*K+full[j-1]][x],a=tensor(full,j,0)[x],b=tensor(full,j,1)[x];lang-=Math.log2(q);g-=Math.log2(a);sh-=Math.log2(b);joint-=Math.log2(.8*q+.2*a);uni-=Math.log2(.8*q+.2/27);shiftJoint-=Math.log2(.8*q+.2*b)}
 const hits=suf.filter((x,i)=>x===truth[i]).length,expect=suf.reduce((t,x)=>t+truth.filter(y=>x===y).length/91,0),shifts=range(91).map(k=>suf.filter((x,i)=>x===truth[(i+k)%91]).length);
 Object.assign(r,{text:s,lang,g,sh,joint,uni,shiftJoint,geometryBenefit:uni-joint,hits,expect,shiftAtLeast:shifts.filter(x=>x>=hits).length,shiftMax:Math.max(...shifts)});}
 const candidates=[...cand.values()];for(const k of ["lang","g","sh","joint","uni","shiftJoint"])for(const [i,r] of candidates.slice().sort((a,b)=>a[k]-b[k]).entries())(r.rank??={})[k]=i+1;
 // All eight role reversals, with a fixed column-major flattening. Matched train-only Huffman models.
 const blockOf=(b,lo,hi)=>b.chapters.filter(ch=>ch.c>=lo&&ch.c<=hi).flatMap(ch=>{const s=charseq(ch);return range(Math.floor(s.length/216)).map(i=>[s.slice(i*216,i*216+72),s.slice(i*216+72,i*216+144),s.slice(i*216+144,i*216+216)])});
 const tr=blockOf(book,1,13),te=blockOf(book,16,40),cr=blockOf(genesis,1,50);
 const vset=new Set(words.filter(w=>[...w].length===3)),allWords=new Set(words);
 function woven(rows,m){const n=rows[0].length;return range(n).flatMap(j=>rows.map((r,i)=>r[(m>>i)&1?n-1-j:j]))}
 function lengths(ct){let ns=ct.map((w,i)=>({w,i,ls:[i]})),l=ct.map(()=>0);while(ns.length>1){ns.sort((a,b)=>a.w-b.w||a.i-b.i);let a=ns.shift(),b=ns.shift();for(const k of a.ls.concat(b.ls))l[k]++;ns.push({w:a.w+b.w,i:Math.min(a.i,b.i),ls:a.ls.concat(b.ls)})}return l}
 function canonical(l){let order=range(27).sort((a,b)=>l[a]-l[b]||a-b),next=0,last=0,c=Array(27);for(const i of order){next*=2**(l[i]-last);c[i]=next.toString(2).padStart(l[i],"0");next++;last=l[i]}return c}
 function fitWeave(m){const counts=range(28).map(()=>Array(27).fill(1));for(const w of tr){const s=woven(w,m);for(let j=0;j<s.length;j++)counts[j?s[j-1]:27][s[j]]++}return counts.map(lengths)}
 function code(ws,m,ls){const c=ls.map(canonical),maps=c.map(t=>new Map(t.map((v,i)=>[v,i])));let payload=0,verified=0,wordHits=0;for(const w of ws){const s=woven(w,m),stream=s.map((x,j)=>c[j?s[j-1]:27][x]).join("");let i=0,out=[];for(let j=0;j<s.length;j++){let map=maps[j?out[j-1]:27],p="";while(i<stream.length&&!map.has(p))p+=stream[i++];if(!map.has(p))throw Error("decode");out.push(map.get(p))}if(i!==stream.length||out.some((x,i)=>x!==s[i]))throw Error("codec");const recovered=w.map((r,k)=>range(r.length).map(j=>out[3*((m>>k)&1?r.length-1-j:j)+k]));if(recovered.some((r,k)=>r.some((x,j)=>x!==w[k][j])))throw Error("weave inverse");payload+=stream.length;verified+=s.length;for(let j=0;j<s.length;j+=3)wordHits+=vset.has(s.slice(j,j+3).map(i=>alphabet[i]).join(""))}return {payload,verified,wordHits,triplets:verified/3,totalBits:payload+3780+3}}
 const native=source.spans.map(w=>({book:w.book,ch:w.ch,v:w.v,rows:w.rows.map(encode)}));
 const orientations=range(8).map(m=>{const ls=fitWeave(m);return {m,directions:range(3).map(i=>(m>>i)&1?"R":"F").join(""),test:code(te,m,ls),cross:code(cr,m,ls),native:native.map(w=>{const s=woven(w.rows,m),ts=range(s.length/3).map(j=>s.slice(3*j,3*j+3).map(i=>alphabet[i]).join(""));return {book:w.book,ch:w.ch,v:w.v,n:ts.length,wordHits:ts.filter(t=>vset.has(t)).length,words:ts.filter(t=>vset.has(t))}})}});

 // Compare chapter-level paired differences, not individual correlated glyphs.
 const pairs={};for(const [label,b,lo,hi] of [["exodus",book,16,40],["genesis",genesis,1,50]]){const l0=fitWeave(0),l2=fitWeave(2),deltas=[];for(const ch of b.chapters.filter(c=>c.c>=lo&&c.c<=hi)){let ws=blockOf({chapters:[ch]},lo,hi);if(ws.length){const a=code(ws,0,l0),b=code(ws,2,l2);deltas.push({chapter:ch.c,blocks:ws.length,delta:a.payload-b.payload})}}
 let seed=0x41369;const rnd=()=>{seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return (seed>>>0)/4294967296};const observed=deltas.reduce((s,x)=>s+x.delta,0);let at=0;for(let i=0;i<16384;i++){const val=deltas.reduce((s,x)=>s+(rnd()<.5?-1:1)*x.delta,0);at+=Math.abs(val)>=Math.abs(observed)}pairs[label]={deltas,observed,positive:deltas.filter(x=>x.delta>0).length,negative:deltas.filter(x=>x.delta<0).length,ties:deltas.filter(x=>x.delta===0).length,signFlipTwoSided:(at+1)/16385,qualification:"Exploratory chapter-cluster sign-flip, symmetric/exchangeable chapter differences assumption, reused corpus; not confirmatory significance."}}
 const segmented="אז ישיר משה ובני ישראל את השירה הזאת ליהוה ויאמרו לאמר אשירה ליהוה כי גאה גאה סוס ורכבו רמה בים עזי וזמרת יה ויהי ל".split(" ");if(segmented.join("")!==previous.actual)throw Error("segmentation");const vocabAudit={completeWords:segmented.length-1,missing:segmented.slice(0,-1).filter(w=>!allWords.has(w)),finalFragment:segmented.at(-1),qualification:"Manually segmented known target, checked glyph concatenation against actual fixture. Final fragment excluded. Exact training surface-form membership, not lexeme or root analysis."};

 return {pairs,vocabAudit,candidates,trainBlocks:tr.length,testBlocks:te.length,crossBlocks:cr.length,orientations,wordTypes3:vset.size,qualification:"Pure geometry is normalized causal residual likelihood with word/char priors removed, candidate rank only among disclosed H40 strings plus actual, not global rank. Geometry benefit relative to matched uniform mixture. Circular shift overlap includes identity and is descriptive, not iid p-value. Orientation test uses actual canonical binary Huffman previous woven glyph context, pseudocount1, 28x27x5 bits tables +3 mode bits, same all orientations; actual encoded/decoded strings plus inverse weave. Known block size and count conditional protocol. Exact three-glyph training word membership is lexical proxy NOT root annotation. No claim of poetry-free test blocks. Prior reused holdouts; no fresh blind."};
}

const base='Docs/support/reference/TorahCryptoCorpus20261125/';console.log(JSON.stringify(assay(...['exodus.normalized.json','exodus-training-words.json','h40-word-tensor.json','h32-chart-independent.json','genesis.normalized.json'].map(n=>JSON.parse(fs.readFileSync(base+n,'utf8')))),null,2));
