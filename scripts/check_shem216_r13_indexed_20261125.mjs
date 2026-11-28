// Exact finite checker; run node scripts/check_shem216_r13_indexed_20261125.mjs
// Fixture is pinned WLC XML, Exodus 14:19–21, source segments preserved.
const fixture = [
  "<v n=\"19\" s=\"E\">\n        <w>וַ/יִּסַּ֞ע</w>\n        <w>מַלְאַ֣ךְ</w>\n        <w>הָ/אֱלֹהִ֗ים</w>\n        <w>הַ/הֹלֵךְ֙</w>\n        <w>לִ/פְנֵי֙</w>\n        <w>מַחֲנֵ֣ה</w>\n        <w>יִשְׂרָאֵ֔ל</w>\n        <w>וַ/יֵּ֖לֶךְ</w>\n        <w>מֵ/אַחֲרֵי/הֶ֑ם</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n      </v>",
  "<v n=\"19\" s=\"J\">\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>וַ/יִּסַּ֞ע</w>\n        <w>עַמּ֤וּד</w>\n        <w>הֶֽ/עָנָן֙</w>\n        <w>מִ/פְּנֵי/הֶ֔ם</w>\n        <w>וַ/יַּֽעֲמֹ֖ד</w>\n        <w>מֵ/אַחֲרֵי/הֶֽם׃</w>\n      </v>",
  "<v n=\"20\" s=\"E\">\n        <w>וַ/יָּבֹ֞א</w>\n        <w>בֵּ֣ין ׀</w>\n        <w>מַחֲנֵ֣ה</w>\n        <w>מִצְרַ֗יִם</w>\n        <w>וּ/בֵין֙</w>\n        <w>מַחֲנֵ֣ה</w>\n        <w>יִשְׂרָאֵ֔ל</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n      </v>",
  "<v n=\"20\" s=\"J\">\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>וַ/יְהִ֤י</w>\n        <w>הֶֽ/עָנָן֙</w>\n        <w>וְ/הַ/חֹ֔שֶׁךְ</w>\n        <w>וַ/יָּ֖אֶר</w>\n        <w>אֶת־</w>\n        <w>הַ/לָּ֑יְלָה</w>\n        <w>וְ/לֹא־</w>\n        <w>קָרַ֥ב</w>\n        <w>זֶ֛ה</w>\n        <w>אֶל־</w>\n        <w>זֶ֖ה</w>\n        <w>כָּל־</w>\n        <w>הַ/לָּֽיְלָה׃</w>\n      </v>",
  "<v n=\"21\" s=\"P\">\n        <w>וַ/יֵּ֨ט</w>\n        <w>מֹשֶׁ֣ה</w>\n        <w>אֶת־</w>\n        <w>יָד/וֹ֮</w>\n        <w>עַל־</w>\n        <w>הַ/יָּם֒</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n      </v>",
  "<v n=\"21\" s=\"J\">\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>.</w>\n        <w>וַ/יּ֣וֹלֶךְ</w>\n        <w>יְהוָ֣ה ׀</w>\n        <w>אֶת־</w>\n        <w>הַ֠/יָּם</w>\n        <w>בְּ/ר֨וּחַ</w>\n        <w>קָדִ֤ים</w>\n        <w>עַזָּה֙</w>\n        <w>כָּל־</w>\n        <w>הַ/לַּ֔יְלָה</w>\n        <w>וַ/יָּ֥שֶׂם</w>\n        <w>אֶת־</w>\n        <w>הַ/יָּ֖ם</w>\n        <w>לֶ/חָרָבָ֑ה</w>\n        <w>וַ/יִּבָּקְע֖וּ</w>\n        <w>הַ/מָּֽיִם׃</w>\n      </v>"
];
function run(fixture){
 const counts={},check=(name,ok)=>{if(!ok)throw Error(name);counts[name]=(counts[name]||0)+1};
 const range=n=>Array.from({length:n},(_,i)=>i),key=x=>JSON.stringify(x),eq=(a,b)=>key(a)===key(b);
 const rows=range(3).map(r=>{
   const seg=fixture.filter(s=>s.includes(`n="${19+r}"`)).map((s,k)=>({label:s.match(/ s="([^"]+)"/)[1],words:[...s.matchAll(/<w>([\s\S]*?)<\/w>/g)].map(x=>x[1])}));
   check("source_segments",seg.length===2&&seg[0].words.length===seg[1].words.length);
   const row=[];
   for(const w of range(seg[0].words.length)){
     const active=seg.map((s,i)=>[s,i]).filter(([s])=>s.words[w]!==".");
     check("source_word_partition",active.length===1);
     const [s,i]=active[0];
     for(const [offset,glyph] of [...s.words[w]].entries())if(/[\u05d0-\u05ea]/u.test(glyph))row.push({r,j:row.length,segment:i,label:s.label,w,offset,glyph});
   }
   check("source_row_length",row.length===72);
   for(const x of row)check("source_coordinate", [...seg[x.segment].words[x.w]][x.offset]===x.glyph);
   return row;
 });
 const all=rows.flat(),triplets=range(72).map(j=>[rows[0][j],rows[1][71-j],rows[2][j]]);
 check("source_triplet_cover",new Set(triplets.flat().map(x=>key([x.r,x.j]))).size===216);
 const glyphs=triplets.map(t=>t.map(x=>x.glyph).join(""));
 const encode=(r,j)=>[r,Math.floor(j/9),Math.floor(j%9/3)-1,j%3-1];
 const decode=([r,q,a,b])=>[r,9*q+3*(a+1)+b+1];
 const C=all.map(x=>encode(x.r,x.j)),lookup=([r,j])=>rows[r][j],neg=([r,q,a,b])=>[2-r,7-q,-a,-b],shem=x=>x[0]===1?neg(x):x,phase=([r,q,a,b])=>[r,q^4,a,b];
 const edge=([r,q,a,b])=>[r,(q>>1)&1,q&1,(q>>2)&1,a,b];
 const unedge=([r,u,v,s,a,b])=>[r,4*s+2*u+v,a,b];
 const p54=([r,q,a,b])=>[q>>2,r-1,a,b],res=([r,q,a,b])=>q&3;
 const lift=([p,r,a,b],k)=>[r+1,4*p+k,a,b];
 const glue=([p,r,a,b])=>r===0&&a===0&&b===0?[0]:[1,p,r,a,b];
 const q53=x=>glue(p54(x)),fibres=new Map(),f54=new Map();
 const phase54=([p,r,a,b])=>[1-p,r,a,b],neg54=([p,r,a,b])=>[1-p,-r,-a,-b],shem54=x=>x[1]===0?neg54(x):x;
 const phase53=x=>x[0]===0?x:[1,1-x[1],...x.slice(2)],neg53=x=>x[0]===0?x:[1,1-x[1],...x.slice(2).map(v=>-v)],shem53=x=>x[0]===0||x[2]!==0?x:neg53(x);
 const ops=[shem,neg,phase],act=(mask,x)=>ops.reduce((y,f,i)=>mask&(1<<i)?f(y):y,x);
 for(const x of C){
   const [r,j]=decode(x),source=lookup([r,j]);
   check("H1_index_roundtrip",eq(encode(r,j),x)&&eq(unedge(edge(x)),x)&&source.r===r&&source.j===j);
   check("H2_shem_reflection",eq(decode(shem(x)),[r,r===1?71-j:j]));
   check("H2_global_antipode",eq(decode(neg(x)),[2-r,71-j]));
   check("H7_54_residual_roundtrip",eq(lift(p54(x),res(x)),x));
   for(const [f,g,h] of [[phase,phase54,phase53],[neg,neg54,neg53],[shem,shem54,shem53]]){
     check("H7_54_equivariance",eq(p54(f(x)),g(p54(x))));
     check("H7_53_equivariance",eq(q53(f(x)),h(q53(x))));
   }
   for(const [map,k] of [[fibres,key(q53(x))],[f54,key(p54(x))]])map.set(k,(map.get(k)||0)+1);
   for(const i of range(3))for(const j of range(3))if(i<j)for(const side of range(2)){
     const z=act(side<<(3-i-j),x);
     check("H8_six_faces",eq(ops[i](ops[j](z)),ops[j](ops[i](z))));
   }
   for(const i of range(8))for(const j of range(8)){
     const y=act(i,x),z=act(j,y);
     check("H8_path_composition",eq(z,act(i^j,x))&&eq(act(i^j,z),x));
     // source provenance is carried by inverse chart, not overwritten by target letter
     check("H8_payload_recovery",eq(lookup(decode(act(i^j,z))),source));
   }
 }
 check("H7_fibre_sizes",f54.size===54&&[...f54.values()].every(n=>n===4)&&fibres.size===53&&fibres.get("[0]")===8&&[...fibres].every(([k,n])=>k==="[0]"||n===4));
 const mod=x=>((x%3)+3)%3, V=range(27).map(i=>[i%3,Math.floor(i/3)%3,Math.floor(i/9)]),zero=[0,0,0],one=[1,0,0],t=[0,1,0];
 const mul=(a,b)=>{let c=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)c[i+j]+=a[i]*b[j];for(let i=4;i>=3;i--){c[i-3]+=c[i];c[i-2]+=c[i]}return c.slice(0,3).map(mod)};
 const pow=(a,n)=>{let r=one;for(let i=0;i<n;i++)r=mul(r,a);return r};
 const minus=x=>x.map(a=>mod(-a)),canon=x=>x.find(a=>a!==0)===2?minus(x):x,axes=V.filter(x=>!eq(x,zero)&&eq(x,canon(x)));
 const inv=x=>eq(x,zero)?zero:pow(x,25),T=x=>mul(t,x),R=x=>inv(x),norm=x=>x.filter(a=>a!==0).length;
 check("H3_field_generator",eq(pow(t,13),one)&&!eq(t,one)&&axes.length===13);
 for(const x of V){
   check("H3_signed_action",eq(R(R(x)),x)&&eq(pow(t,13),one)&&eq(R(T(R(x))),mul(pow(t,12),x)));
   check("H3_sign_equivariance",eq(R(minus(x)),minus(R(x)))&&eq(T(minus(x)),minus(T(x))));
   if(!eq(x,zero))check("H3_field_inverse",eq(mul(x,inv(x)),one));
 }
 const chart=i=>canon(pow(t,(i+10)%13)),fixed=axes.filter(x=>eq(canon(R(x)),x));
 for(const i of range(13))check("H3_keyshoe_bidi",eq(canon(T(chart(i))),chart((i+1)%13))&&eq(canon(R(chart(i))),chart((19-i)%13)));
 check("H3_unique_axis",fixed.length===1&&eq(fixed[0],one)&&new Set(range(13).map(i=>key(chart(i)))).size===13);
 const dot=(a,b)=>mod(a.reduce((s,x,i)=>s+x*b[i],0));
 const lines=axes.map(n=>axes.filter(x=>dot(n,x)===0).map(key).sort());
 const invLines=lines.map(line=>line.map(k=>key(canon(R(JSON.parse(k))))).sort());
 const lineFailures=invLines.map((l,i)=>[i,l]).filter(([i,l])=>!lines.some(m=>eq(l,m)));
 check("H3_incidence_negative",lineFailures.length>0);
 const shells=range(4).map(k=>V.filter(x=>norm(x)===k).length);
 check("H4_shells",eq(shells,[1,6,12,8]));
 const edgeCenters=V.filter(x=>norm(x)===2), pairs=edgeCenters.filter(x=>eq(canon(x),x));
 check("H4_edge_antipodes",pairs.length===6&&edgeCenters.every(x=>!eq(x,minus(x))));
 const directionFibres=range(3).map(i=>edgeCenters.filter(x=>x[i]===0));
 check("H4_parallel_edges",directionFibres.every(xs=>xs.length===4));
 // Marked-axis reflection-only chart, not an incidence or rotation weld.
 const marked=new Map([[key(one),null]]);
 for(const [k,x] of pairs.entries()){marked.set(key(chart((3+k+1)%13)),x);marked.set(key(chart((3-k-1+13)%13)),minus(x))}
 for(const x of axes){const y=marked.get(key(x)),z=marked.get(key(canon(R(x))));check("H6_marked_reflection",y===null?z===null:eq(minus(y),z))}
 check("H6_rotation_not_mark_preserving",!eq(canon(T(one)),one));
 return {counts,distinctTripletsRaw:new Set(glyphs).size,distinctTripletsFinalFold:new Set(glyphs.map(s=>s.replace(/[ךםןףץ]/g,c=>({"ך":"כ","ם":"מ","ן":"נ","ף":"פ","ץ":"צ"})[c]))).size,firstTriplet:glyphs[0],lastTriplet:glyphs[71],shells,incidenceLinesPreserved:13-lineFailures.length,incidenceCounterexample:{line:lines[lineFailures[0][0]].map(JSON.parse),image:lineFailures[0][1].map(JSON.parse)},fiber54:4,fiber53:{zero:8,nonzero:4}};
}
console.log(JSON.stringify(run(fixture), null, 2));
