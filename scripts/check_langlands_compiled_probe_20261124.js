// Langlands R164–R169 exact source/compiled/weighted probe regression.
function run(){
 const assert=(b,m)=>{if(!b)throw Error(m)};
 const Z=[];let k=0;const digits="16763747126132141175";
 for(let i=1;i<=6;i++)for(let j=i+1;j<=6;j++)for(let l=j+1;l<=6;l++)Z.push([i,j,l].map((v,h)=>((+digits[k]>>h)&1)?-v:v)),k++;
 const truth=(F,x)=>F.every(c=>c.some(l=>x[Math.abs(l)]===+(l>0)));
 assert(Array.from({length:64},(_,x)=>[undefined,...Array.from({length:6},(_,i)=>(x>>i)&1)]).filter(x=>truth(Z,x)).map(x=>x.slice(1).join("")).join()==="000000","zero gadget");
 function compile(q,F){
  let n=q;const G=[],ops=[];
  function gate(a,b,op){const y=++n;ops.push([op,y,a,b]);G.push(...(op==="or"?[[-a,y],[-b,y],[a,b,-y]]:[[a,-y],[b,-y],[-a,-b,y]]));return y}
  const out=F.map(c=>c.slice(1).reduce((a,b)=>gate(a,b,"or"),c[0]));
  const a=out.length?out.slice(1).reduce((a,b)=>gate(a,b,"and"),out[0]):0;
  const flag=++n;ops.push(["flag",flag,a,0]);G.push(...(a?[[-a,flag],[a,-flag]]:[[flag]]));
  const C=Z.map(c=>c.slice()),copies=[];let v=6+n;
  for(const c of G){const L=[];for(const l of c){const x=6+Math.abs(l),u=++v;C.push([-x,u,1],[x,-u,2]);copies.push([u,x]);L.push(l>0?u:-u)}while(L.length<3)L.push(L.length===1?1:2);C.push(L)}
  assert(C.every(c=>c.length===3&&new Set(c.map(Math.abs)).size===3),"scope");
  assert(new Set(C.map(c=>c.map(Math.abs).sort((a,b)=>a-b).join())).size===C.length,"distinct scopes");
  function lift(bits){const y=[undefined,...bits];const val=l=>l>0?y[l]:1-y[-l];for(const [op,u,a,b] of ops)y[u]=op==="flag"?(a?val(a):1):op==="or"?(val(a)|val(b)):(val(a)&val(b));const x=[undefined,0,0,0,0,0,0,...y.slice(1)];for(const [u,v] of copies)x[u]=x[v];return x}
  return {C,v,flag:flag+6,lift};
 }
 function unit(c,bits){const x=Array(c.v+1).fill(-1);for(let i=1;i<=6;i++)x[i]=0;bits.forEach((v,i)=>x[i+7]=v);let change=true;while(change){change=false;for(const clause of c.C){if(clause.some(l=>x[Math.abs(l)]===+(l>0)))continue;const u=clause.filter(l=>x[Math.abs(l)]===-1);assert(u.length,"conflict");if(u.length===1){x[Math.abs(u[0])]=+(u[0]>0);change=true}}}assert(x.slice(1).every(v=>v>=0),"not forced");return x}
 // R85 actual coefficient ring: (Z/8)[X]/(X^3+X+1).
 const R=(a,b,c)=>[a&7,b&7,c&7],zero=R(0,0,0),one=R(1,0,0);
 const add=(a,b)=>R(a[0]+b[0],a[1]+b[1],a[2]+b[2]),neg=a=>R(-a[0],-a[1],-a[2]),sub=(a,b)=>add(a,neg(b)),scale=(a,n)=>R(...a.map(x=>x*n)),eq=(a,b)=>a.every((x,i)=>x===b[i]);
 function mul(a,b){let t=[0,0,0,0,0];for(let i=0;i<3;i++)for(let j=0;j<3;j++)t[i+j]+=a[i]*b[j];for(let k=4;k>=3;k--){t[k-3]-=t[k];t[k-2]-=t[k]}return R(...t)}
 function pow(a,n){let v=one;while(n){if(n&1)v=mul(v,a);a=mul(a,a);n>>=1}return v}
 const z=Array.from({length:7},(_,i)=>pow(R((i+1)&1,((i+1)>>1)&1,((i+1)>>2)&1),8));z.forEach(v=>assert(eq(pow(v,7),one),"Teich lift"));
 let seed=164;const rnd=n=>{seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return (seed>>>0)%n};
 function packet(q,F,w,pins=new Map()){
  const groups=new Map(),last=Array(F.length).fill(-1);
  for(let i=1;i<=q;i++){
   let p=0n,n=0n;F.forEach((c,j)=>{if(c.includes(i))p|=1n<<BigInt(j);if(c.includes(-i))n|=1n<<BigInt(j)});
   const key=p+","+n;if(!groups.has(key))groups.set(key,{p,n,ids:[]});groups.get(key).ids.push(i)
  }
  const gs=[...groups.values()];gs.forEach((g,t)=>F.forEach((_,j)=>{if((g.p|g.n)&(1n<<BigInt(j)))last[j]=t}));
  if(last.includes(-1))return {v:zero,s:false,peak:0};
  const ins=(D,k,v)=>D.set(k,add(D.get(k)||zero,v));
  let D=new Map([[0n,one]]),peak=1;
  gs.forEach((g,t)=>{
   let L=new Map([[0,one]]);
   for(const i of g.ids){const N=new Map();for(const [f,v] of L)for(const b of pins.has(i)?[pins.get(i)]:[0,1])ins(N,f|(b?2:1),mul(v,w[i][b]));L=N}
   let end=0n;last.forEach((t0,j)=>{if(t===t0)end|=1n<<BigInt(j)});
   const N=new Map();for(const [s,v] of D)for(const [f,u] of L){let t=s|((f&2)?g.p:0n)|((f&1)?g.n:0n);if((t&end)===end)ins(N,t&~end,mul(v,u))}
   D=N;peak=Math.max(peak,D.size);
  });
  return {v:D.get(0n)||zero,s:D.has(0n),peak};
 }
 const allw=(q,w)=>Array.from({length:q},(_,i)=>add(...w[i+1])).reduce(mul,one);
 const ww=(q)=>[null,...Array.from({length:q},()=>[one,z[rnd(7)]])];
 const D=(A,P)=>sub(scale(A,3),scale(P,4));
 let lifts=0,weighted=0,loss=0,faces=0,paths=0,neutral=0;
 const perms=[[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]];
 for(let t=0;t<100;t++){
  const q=1+rnd(6),F=Array.from({length:rnd(8)},()=>Array.from({length:1+rnd(3)},()=> (rnd(2)?1:-1)*(1+rnd(q))));
  const c=compile(q,F),w=ww(q),A=allw(q,w);let P=zero,inh=false;
  const Q=Array.from({length:1+rnd(3)},()=> (rnd(2)?1:-1)*(1+rnd(q))), pins=new Map();let conflict=false;
  for(const l of Q){const i=Math.abs(l),b=+(l<0);if(pins.has(i)&&pins.get(i)!==b)conflict=true;pins.set(i,b)}
  let L=zero;
  for(let x=0;x<2**q;x++){const b=Array.from({length:q},(_,i)=>(x>>i)&1),xx=[undefined,...b],y=c.lift(b),u=unit(c,b);
   assert(truth(c.C,y)&&y.slice(1).every((v,i)=>v===u[i+1])&&y[c.flag]===+truth(F,xx),"compiled unique lift");lifts++;
   const v=b.reduce((v,b,i)=>mul(v,w[i+1][b]),one);
   if(y[c.flag]){P=add(P,v);inh=true;if(!truth([Q],xx))L=add(L,v)}
  }
  const p=packet(q,F,w),p1=packet(q,[...F,Q],w),l=conflict?zero:packet(q,F,w,pins).v;
  assert(eq(P,p.v)&&inh===p.s,"source packet");assert(eq(l,L)&&eq(p1.v,sub(P,L))&&eq(sub(D(A,p1.v),D(A,P)),scale(L,4)),"loss scalar");weighted++;loss++;
  if(p.s&&eq(p.v,zero))neutral++;
  // cube: add Q, compile flag graph, reduce coefficients mod2 after forming D
  // retain source and applied flags; compilation changes representation only.
  function obs(mask){let f=(mask&1)?[...F,Q]:F;let pp=packet(q,f,w).v;
   if(mask&2){const cc=compile(q,f);let v=zero;for(let x=0;x<2**q;x++){const b=Array.from({length:q},(_,i)=>(x>>i)&1);if(cc.lift(b)[cc.flag])v=add(v,b.reduce((v,b,i)=>mul(v,w[i+1][b]),one))}assert(eq(v,pp),"compiled obs");pp=v}
   return (mask&4)?pp.map(x=>x&1):pp;
  }
  const cache=Array.from({length:8},(_,m)=>obs(m));
  for(let i=0;i<3;i++)for(let j=i+1;j<3;j++)for(const m of [0,7^(1<<i)^(1<<j)]){
   // compare independently evaluated representation and projection to direct original oracle
   const a=m|(1<<i)|(1<<j),expected=(a&1)?p1.v:P;assert(eq(cache[a],(a&4)?expected.map(x=>x&1):expected),"cube vertex");faces++;
  }
  for(const order of perms){let m=0;for(const i of order)m|=1<<i;assert(eq(cache[m],p1.v.map(x=>x&1)),"path terminal");paths++}
 }
 function cycle(m,n){return Array.from({length:m},(_,j)=>[...Array.from({length:n},(_,i)=>j*n+i+1),...Array.from({length:n},(_,i)=>-(((j+1)%m)*n+i+1))])}
 const large=[];
 for(const [m,n] of [[12,8],[24,8],[48,8]]){const q=m*n,F=cycle(m,n),c=compile(q,F),w=ww(q),p=packet(q,F,w);
  // Independent 3-sector transfer with ring-valued group masses.
  const mulM=(A,B)=>A.map(r=>B[0].map((_,j)=>r.reduce((s,v,k)=>add(s,mul(v,B[k][j])),zero)));
  let T=Array.from({length:3},(_,i)=>Array.from({length:3},(_,j)=>i===j?one:zero));
  for(let j=0;j<m;j++){let a=one,b=one,s=one;for(let i=1;i<=n;i++){const v=w[j*n+i];a=mul(a,v[0]);b=mul(b,v[1]);s=mul(s,add(...v))}const mass=[a,b,sub(sub(s,a),b)];T=mulM(T,Array.from({length:3},(_,i)=>Array.from({length:3},(_,k)=>i===0&&k===1?zero:mass[k])))}
  const tr=T.reduce((a,r,i)=>add(a,r[i]),zero);assert(eq(tr,p.v),"large cyclic probe");
  for(let h=0;h<3;h++){const b=Array.from({length:q},()=>rnd(2)),x=c.lift(b);assert(truth(c.C,x)&&x[c.flag]===+truth(F,[undefined,...b]),"large lift")}
  large.push({q,compiledVars:c.v,clauses:c.C.length,peak:p.peak,P:p.v,D:D(allw(q,w),p.v)});
 }
 return {lifts,weighted,loss,faces,paths,neutral,large,zeroGadget:64,teich:7};
}
console.log(JSON.stringify(run(),null,2));
