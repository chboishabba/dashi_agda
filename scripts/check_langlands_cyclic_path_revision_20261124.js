// Langlands R177–R183: three-sector cyclic path transport, incremental products, precision taper.
function run(){
 const ck=(v,m)=>{if(!v)throw Error(m)};
 let seed=177;const rnd=n=>{seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return (seed>>>0)%n};
 function ring(mod){
  const R=a=>[0,1,2].map(i=>((a[i]||0)%mod+mod)%mod),z=R([]),o=R([1]),add=(a,b)=>R(a.map((v,i)=>v+b[i])),sub=(a,b)=>R(a.map((v,i)=>v-b[i])),scale=(a,n)=>R(a.map(v=>v*n)),eq=(a,b)=>a.every((v,i)=>v===b[i]);
  function mul(a,b){const t=Array(5).fill(0);for(let i=0;i<3;i++)for(let j=0;j<3;j++)t[i+j]+=a[i]*b[j];for(let k=4;k>=3;k--){t[k-3]-=t[k];t[k-2]-=t[k]}return R(t)}
  function pow(a,n){let v=o;while(n){if(n&1)v=mul(v,a);a=mul(a,a);n>>=1}return v}
  return {R,z,o,add,sub,scale,eq,mul,pow};
 }
 const r=ring(32),{R,z,o,add,sub,scale,eq,mul,pow}=r,teich=Array.from({length:7},(_,i)=>pow(R([(i+1)&1,((i+1)>>1)&1,((i+1)>>2)&1]),32));
 teich.forEach(v=>ck(eq(pow(v,7),o),"Teich"));
 const item=(v,s)=>({v,s}),zero=item(z,false),one=item(o,true),plus=(a,b)=>item(add(a.v,b.v),a.s||b.s),times=(a,b)=>item(mul(a.v,b.v),a.s&&b.s),same=(a,b)=>eq(a.v,b.v)&&a.s===b.s;
 let products=0;
 const I=()=>Array.from({length:3},(_,i)=>Array.from({length:3},(_,j)=>i===j?one:zero));
 function mm(A,B){products++;return A.map(row=>B[0].map((_,j)=>row.reduce((a,x,k)=>plus(a,times(x,B[k][j])),zero)))}
 const trace=A=>A.reduce((a,row,i)=>plus(a,row[i]),zero);
 function masses(w,pins=new Map()){
  let f=[one,zero,zero,zero];
  for(let i=0;i<w.length;i++){const g=Array(4).fill(zero);for(let s=0;s<4;s++)for(const b of pins.has(i)?[pins.get(i)]:[0,1])g[s|(b?2:1)]=plus(g[s|(b?2:1)],times(f[s],item(w[i][b],true)));f=g}
  return [f[1],f[2],f[3]];
 }
 const transfer=m=>Array.from({length:3},(_,i)=>Array.from({length:3},(_,j)=>i===0&&j===1?zero:m[j]));
 function tree(A){
  let n=1;while(n<A.length)n*=2;const t=Array(2*n);for(let i=0;i<n;i++)t[n+i]=A[i]||I();for(let i=n-1;i;i--)t[i]=mm(t[2*i],t[2*i+1]);
  return {root:()=>t[1],set(i,M){let k=n+i;t[k]=M;while((k>>=1)>0)t[k]=mm(t[2*k],t[2*k+1])},range(l,h){let a=I(),b=I();for(l+=n,h+=n;l<h;l>>=1,h>>=1){if(l&1)a=mm(a,t[l++]);if(h&1)b=mm(t[--h],b)}return mm(a,b)}};
 }
 function direct(A){return trace(A.reduce(mm,I()))}
 function brute(w,pins){
  const m=w.length,n=w[0].length,q=m*n;let out=zero;
  for(let x=0;x<2**q;x++){let ok=true,v=o;const ss=[];
   for(let j=0;j<m;j++){let f=0;for(let k=0;k<n;k++){const b=(x>>(j*n+k))&1;if(pins[j].has(k)&&pins[j].get(k)!==b)ok=false;f|=b?2:1;v=mul(v,w[j][k][b])}ss.push(f===1?0:f===2?1:2)}
   for(let j=0;j<m;j++)if(ss[j]===0&&ss[(j+1)%m]===1)ok=false;
   if(ok)out=plus(out,item(v,true));
  }return out;
 }
 function pureDelta(A,B){return A.map((row,i)=>row.map((x,j)=>item(sub(B[i][j].v,x.v),false)))}
 const env=(T,i,m)=>mm(T.range(i+1,m),T.range(0,i));
 function coeff(E,j){let v=z;for(let i=0;i<3;i++)if(!(i===0&&j===1))v=add(v,E[j][i].v);return v}
 function v2(v,H){let s=0;while(s<H&&v.every(x=>x%(2**(s+1))===0))s++;return s}
 function Hred(v,H){return v.map(x=>x%(2**H))}
 let small=0,mixed=0,incremental=0,precision=0,scalarProbe=0,support=0,neutral=0,saved=0,budget=0;const large=[];
 function fixture(m,n,smallFlag){
  const w=Array.from({length:m},()=>Array.from({length:n},()=>smallFlag&&rnd(3)===0?[R([rnd(32),rnd(32),rnd(32)]),R([rnd(32),rnd(32),rnd(32)])]:[o,teich[rnd(7)]]));
  const p=Array.from({length:m},()=>new Map()),M=w.map((v,i)=>masses(v,p[i])),A=M.map(transfer),T=tree(A),base=trace(T.root());
  ck(same(base,direct(A)),"base trace");if(smallFlag){ck(same(base,brute(w,p)),"base original");small++}
  let i=rnd(m),j=(i+1+rnd(m-1))%m;if(i>j)[i,j]=[j,i];
  const pi=new Map([[rnd(n),rnd(2)]]),pj=new Map([[rnd(n),rnd(2)]]),mi=masses(w[i],pi),mj=masses(w[j],pj),Bi=transfer(mi),Bj=transfer(mj);
  const Ei=env(T,i,m),Di=pureDelta(A[i],Bi),Dj=pureDelta(A[j],Bj);
  const dv=trace(mm(Di,Ei)).v;
  const P=T.range(0,i),Q=T.range(i+1,j),S=T.range(j+1,m);
  const joint=trace(mm(mm(mm(mm(P,Bi),Q),Bj),S));
  const cross=trace(mm(mm(mm(mm(P,Di),Q),Dj),S)).v;
  const dj=trace(mm(Dj,env(T,j,m))).v;
  ck(eq(joint.v,add(add(add(base.v,dv),dj),cross)),"mixed signed residual");mixed++;
  const before=products;T.set(i,Bi);const ui=products-before,a1=trace(T.root());ck(eq(a1.v,add(base.v,dv)),"single update");
  const before2=products;T.set(j,Bj);const uj=products-before2,a2=trace(T.root());ck(same(a2,joint),"joint update support");incremental+=2;
  p[i]=pi;p[j]=pj;const A2=A.slice();A2[i]=Bi;A2[j]=Bj;ck(same(a2,direct(A2)),"rebuild");support++;
  if(smallFlag){ck(same(a2,brute(w,p)),"joint original");small++}
  // Actual weighted loss and source support: negate one pin in each edited region.
  const altI=transfer(masses(w[i],new Map([...pi].map(([k,v])=>[k,1-v]))));
  const altJ=transfer(masses(w[j],new Map([...pj].map(([k,v])=>[k,1-v]))));
  const lossI=trace(mm(mm(mm(P,altI),Q),mm(A[j],S)));
  const lossJ=trace(mm(mm(mm(P,A[i]),Q),mm(altJ,S)));
  const lossBoth=trace(mm(mm(mm(P,altI),Q),mm(altJ,S)));
  ck(eq(a2.v,add(sub(sub(base.v,lossI.v),lossJ.v),lossBoth.v)),"source loss ledger");
  if(smallFlag){const p0=Array.from({length:m},()=>new Map());p0[i]=new Map([...pi].map(([k,v])=>[k,1-v]));ck(same(lossI,brute(w,p0)),"loss support");p0[j]=new Map([...pj].map(([k,v])=>[k,1-v]));ck(same(lossBoth,brute(w,p0)),"shared loss support");small+=2}
  for(let H=1;H<=3;H++){
   let dv2=z;
   for(let k=0;k<3;k++){const e=coeff(Ei,k),s=v2(e,H),b=H-s,delta=sub(mi[k].v,M[i][k].v),trunc=Hred(delta,b);dv2=add(dv2,mul(e,trunc));saved+=s;budget+=H;ck(eq(Hred(mul(e,delta),H),Hred(mul(e,trunc),H)),"entry taper");precision++}
   ck(eq(Hred(dv2,H),Hred(dv,H)),"scalar taper");precision++;
   // Weil D precision H+2, baseline A fixed for clause/pin filtering.
   const A0=w.flat().reduce((a,v)=>mul(a,add(...v)),o),D0=sub(scale(A0,3),scale(base.v,4)),D1=sub(scale(A0,3),scale(a1.v,4));
   const deltaD=Hred(sub(D1,D0),H+2);ck(deltaD.every(v=>v%4===0)&&eq(deltaD.map(v=>v/4),Hred(scale(dv,-1),H)),"Weil residual");scalarProbe++;
  }
  if(base.s&&eq(Hred(base.v,1),z))neutral++;
  return {m,n,guards:m*n,updateProducts:[ui,uj],buildProducts:2**Math.ceil(Math.log2(m))-1,base:base.v,after:a2.v,inhabited:a2.s};
 }
 for(let t=0;t<100;t++)fixture(3+rnd(2),1+rnd(2),true);
 for(const m of [12,48,192])large.push(fixture(m,8,false));
 return {small,mixed,incremental,precision,scalarProbe,support,neutral,saved,budget,teich:7,large};
}
console.log(JSON.stringify(run(),null,2));
