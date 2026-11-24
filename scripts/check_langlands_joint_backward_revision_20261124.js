// Langlands R170 onward: original factor-tree joint environments and signed revision.
function run(){
 const ck=(x,m)=>{if(!x)throw Error(m)};
 let seed=170;const rnd=n=>{seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return (seed>>>0)%n};
 function ring(mod){
  const R=t=>[0,1,2].map(i=>((t[i]||0)%mod+mod)%mod),z=R([]),o=R([1]);
  const add=(a,b)=>R(a.map((v,i)=>v+b[i])),sub=(a,b)=>R(a.map((v,i)=>v-b[i])),scale=(a,k)=>R(a.map(v=>v*k)),eq=(a,b)=>a.every((v,i)=>v===b[i]);
  function mul(a,b){let t=Array(5).fill(0);for(let i=0;i<3;i++)for(let j=0;j<3;j++)t[i+j]+=a[i]*b[j];for(let k=4;k>=3;k--){t[k-3]-=t[k];t[k-2]-=t[k]}return R(t)}
  function pow(a,n){let v=o;while(n){if(n&1)v=mul(v,a);a=mul(a,a);n>>=1}return v}
  return {R,z,o,add,sub,scale,eq,mul,pow};
 }
 const r8=ring(8),teich=Array.from({length:7},(_,i)=>r8.pow(r8.R([(i+1)&1,((i+1)>>1)&1,((i+1)>>2)&1]),8));
 teich.forEach(z=>ck(r8.eq(r8.pow(z,7),r8.o),"Teich"));
 const bits=(n,x)=>Array.from({length:n},(_,i)=>(x>>i)&1);
 const proj=(x,src,dst)=>dst.reduce((v,j,i)=>v|(((x>>src.indexOf(j))&1)<<i),0);
 const sat=(F,x)=>F.every(c=>c.some(l=>x[Math.abs(l)-1]===+(l>0)));
 function build(n,F,w,r,order=Array.from({length:n},(_,i)=>i)){
  const {z,o,add,mul}=r;const nodes=[],cl=[],bags=[];let ops=0,rev=0,peak=0;
  function node(scope,v,s,kind,children=[]){const a={scope,v,s,kind,children,e:v.map(()=>z),t:v.map(()=>false)};nodes.push(a);peak=Math.max(peak,scope.length);return a}
  let live=w.map((v,i)=>node([i],v,[true,true],"leaf"));
  for(const c of F){const scope=[...new Set(c.map(l=>Math.abs(l)-1))].sort((a,b)=>a-b);
   const s=Array.from({length:2**scope.length},(_,x)=>c.some(l=>((x>>scope.indexOf(Math.abs(l)-1))&1)===+(l>0)));
   const a=node(scope,s.map(b=>b?o:z),s,"leaf");cl.push(a);live.push(a)}
  function product(fs){const scope=[...new Set(fs.flatMap(f=>f.scope))].sort((a,b)=>a-b);
   const v=[],s=[];for(let x=0;x<2**scope.length;x++){let a=o,b=true;for(const f of fs){const k=proj(x,scope,f.scope);a=mul(a,f.v[k]);b=b&&f.s[k];ops++}v.push(a);s.push(b)}
   return node(scope,v,s,"prod",fs);
  }
  for(const i of order){const fs=live.filter(f=>f.scope.includes(i));live=live.filter(f=>!f.scope.includes(i));ck(fs.length,"missing weight");const p=product(fs);bags.push(p);const scope=p.scope.filter(j=>j!==i),v=Array(2**scope.length).fill(z),s=Array(v.length).fill(false);
   for(let x=0;x<p.v.length;x++){const k=proj(x,p.scope,scope);v[k]=add(v[k],p.v[x]);s[k]=s[k]||p.s[x];ops++}live.push(node(scope,v,s,"sum",[p]));
  }
  const root=product(live);ck(root.scope.length===0,"root");root.e[0]=o;root.t[0]=true;
  for(const a of nodes.slice().reverse()){
   if(a.kind==="sum"){const f=a.children[0];for(let x=0;x<f.v.length;x++){const k=proj(x,f.scope,a.scope);f.e[x]=add(f.e[x],a.e[k]);f.t[x]=f.t[x]||a.t[k];rev++}}
   if(a.kind==="prod")for(let x=0;x<a.v.length;x++){
    const fs=a.children,ks=fs.map(f=>proj(x,a.scope,f.scope));const pre=[o],ps=[true],suf=Array(fs.length+1),ss=Array(fs.length+1);suf[fs.length]=o;ss[fs.length]=true;
    for(let i=0;i<fs.length;i++){pre.push(mul(pre[i],fs[i].v[ks[i]]));ps.push(ps[i]&&fs[i].s[ks[i]]);rev++}
    for(let i=fs.length-1;i>=0;i--){suf[i]=mul(fs[i].v[ks[i]],suf[i+1]);ss[i]=fs[i].s[ks[i]]&&ss[i+1];rev++}
    for(let i=0;i<fs.length;i++){const f=fs[i],k=ks[i];f.e[k]=add(f.e[k],mul(a.e[x],mul(pre[i],suf[i+1])));f.t[k]=f.t[k]||(a.t[x]&&ps[i]&&ss[i+1]);rev+=3}
   }
  }
  return {root,bags,cl,ops,rev,peak};
 }
 function brute(n,F,w,r,scope=[],k=0){
  let v=r.z,s=false;
  for(let u=0;u<2**n;u++){const x=bits(n,u);if(proj(u,Array.from({length:n},(_,i)=>i),scope)!==k||!sat(F,x))continue;s=true;v=r.add(v,x.reduce((a,b,i)=>r.mul(a,w[i][b]),r.o))}
  return {v,s};
 }
 let scalar=0,joint=0,revision=0,neutral=0,precision=0,cross=0;const large=[];
 for(let t=0;t<100;t++){
  const n=1+rnd(6),F=Array.from({length:rnd(9)},()=>Array.from({length:rnd(4)},()=> (rnd(2)?1:-1)*(1+rnd(n))));
  if(t%4===0)F.splice(0,F.length,...Array.from({length:n},(_,i)=>[i+1,-((i+1)%n+1)]));
  const w=Array.from({length:n},()=>t%2?[r8.o,teich[rnd(7)]]:[r8.R([rnd(8),rnd(8),rnd(8)]),r8.R([rnd(8),rnd(8),rnd(8)])]);
  const full=build(n,F,w,r8);
  for(const m of [8,4,2]){
   const r=ring(m),ww=w.map(v=>v.map(r.R)),a=build(n,F,ww,r),b=brute(n,F,ww,r);
   ck(r.eq(a.root.v[0],b.v)&&a.root.s[0]===b.s,"scalar");scalar++;
   ck(r.eq(a.root.v[0],r.R(full.root.v[0])),"precision");precision++;
   for(let j=0;j<a.bags.length;j++){const f=a.bags[j];for(let k=0;k<f.v.length;k++){
     const b=brute(n,F,ww,r,f.scope,k),v=r.mul(f.v[k],f.e[k]),s=f.s[k]&&f.t[k];
     ck(r.eq(v,b.v)&&s===b.s,"joint");ck(r.eq(v,r.R(r8.mul(full.bags[j].v[k],full.bags[j].e[k]))),"joint precision");joint++;precision++;if(s&&r.eq(v,r.z))neutral++;
    }
    // append two arbitrary signed clauses supported in a bag; exact gain/loss and mixed correction
    const C=f.scope.map(i=> (rnd(2)?1:-1)*(i+1)),D=f.scope.filter(()=>rnd(2)).map(i=> (rnd(2)?1:-1)*(i+1));
    let l=r.z,h=r.z,mix=r.z;
    for(let k=0;k<f.v.length;k++){const fail=c=>!c.some(l=>((k>>f.scope.indexOf(Math.abs(l)-1))&1)===+(l>0)),v=r.mul(f.v[k],f.e[k]);if(fail(C))l=r.add(l,v);if(fail(D))h=r.add(h,v);if(fail(C)&&fail(D))mix=r.add(mix,v)}
    const p=a.root.v[0],pC=brute(n,[...F,C],ww,r).v,pD=brute(n,[...F,D],ww,r).v,pCD=brute(n,[...F,C,D],ww,r).v;
    ck(r.eq(r.sub(p,pC),l)&&r.eq(r.sub(p,pD),h)&&r.eq(r.add(r.sub(r.sub(p,l),h),mix),pCD),"mixed");cross++;
   }
   for(let j=0;j<F.length;j++){const f=a.cl[j];let gain=r.z,inh=false;
    for(let k=0;k<f.v.length;k++)if(!f.s[k]){gain=r.add(gain,f.e[k]);inh=inh||f.t[k]}
    const rest=F.filter((_,i)=>i!==j),p=brute(n,rest,ww,r),g=brute(n,[...rest,...F[j].map(l=>[-l])],ww,r);
    ck(r.eq(r.add(a.root.v[0],gain),p.v)&&r.eq(gain,g.v)&&inh===g.s,"delete");
    const A=ww.reduce((v,w)=>r.mul(v,r.add(...w)),r.o),d0=r.sub(r.scale(A,3),r.scale(a.root.v[0],4)),d1=r.sub(r.scale(A,3),r.scale(p.v,4));
    ck(r.eq(r.sub(d1,d0),r.scale(gain,-4)),"Weil delete");revision++;
   }
  }
 }
 // Large cyclic width-two source, independent trace and all unit/edge bag marginals via direct pinned trace.
 for(const n of [12,48,192]){
  const F=Array.from({length:n},(_,i)=>[i+1,-((i+1)%n+1)]),w=Array.from({length:n},()=>[r8.o,teich[rnd(7)]]),a=build(n,F,w,r8);
  function trace(pins){
   let T=[[r8.o,r8.z],[r8.z,r8.o]];
   for(let j=0;j<n;j++){const k=(j+1)%n,M=Array.from({length:2},(_,x)=>Array.from({length:2},(_,y)=>(x===0&&y===1)||(pins.has(k)&&pins.get(k)!==y)?r8.z:w[k][y]));
    T=T.map(row=>[0,1].map(c=>r8.add(r8.mul(row[0],M[0][c]),r8.mul(row[1],M[1][c]))))}
   return r8.add(T[0][0],T[1][1]);
  }
  ck(r8.eq(a.root.v[0],trace(new Map())),"large trace");let checked=0;
  for(const f of a.bags){for(let k=0;k<f.v.length;k++){const pins=new Map(f.scope.map((i,j)=>[i,(k>>j)&1]));ck(r8.eq(r8.mul(f.v[k],f.e[k]),trace(pins)),"large marginal");checked++}}
  large.push({n,peak:a.peak,forward:a.ops,reverse:a.rev,entries:checked});
 }
 return {scalar,joint,revision,neutral,precision,cross,teich:7,large};
}
console.log(JSON.stringify(run(),null,2));
