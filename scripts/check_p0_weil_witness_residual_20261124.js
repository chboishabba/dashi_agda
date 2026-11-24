// G115–G120: Langlands donor, P vs NP endpoint. Exact regression; node script.
function run(){
 const ck=(a,m)=>{if(!a)throw Error(m)};
 const d=5,zero=[0,0,0,0,0],one=[1,0,0,0,0],R=a=>Array.from({length:d},(_,i)=>(a[i]||0)&7);
 const add=(a,b)=>R(a.map((v,i)=>v+b[i])),sub=(a,b)=>R(a.map((v,i)=>v-b[i])),scale=(a,n)=>R(a.map(v=>v*n)),eq=(a,b)=>a.every((v,i)=>v===b[i]),res=a=>a.map(v=>v&1),nz=a=>a.some(Boolean);
 function mul(a,b){const t=Array(9).fill(0);for(let i=0;i<d;i++)for(let j=0;j<d;j++)t[i+j]+=a[i]*b[j];for(let k=8;k>=5;k--){t[k-5]-=t[k];t[k-3]-=t[k]}return R(t)}
 function pow(a,n){let v=one;while(n){if(n&1)v=mul(v,a);a=mul(a,a);n>>=1}return v}
 const z=Array.from({length:31},(_,i)=>pow(R(Array.from({length:d},(_,j)=>((i+1)>>j)&1)),32));
 z.forEach((v,i)=>ck(eq(pow(v,31),one)&&res(v).every((b,j)=>b===(((i+1)>>j)&1)),"Teich"));
 let seed=115;const rnd=n=>{seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return (seed>>>0)%n};
 const sat=(F,x)=>F.every(c=>c.some(l=>x[Math.abs(l)-1]===+(l>0)));
 const val=(x,w)=>x.reduce((a,b,i)=>mul(a,b?w[i]:one),one);
 function brute(F,n,w,p){let P=zero,A=zero,inh=false;for(let u=0;u<2**n;u++){const x=Array.from({length:n},(_,i)=>(u>>i)&1);if(p.some((b,i)=>b!==x[i]))continue;const v=val(x,w);A=add(A,v);if(sat(F,x)){P=add(P,v);inh=true}}return {A,P,inh}}
 function contract(F,n,w,p){
   const A=w.reduce((v,z,i)=>mul(v,i<p.length?(p[i]?z:one):add(one,z)),one);
   if(F.some(c=>!c.length))return {A,P:zero,inh:false,peak:0};
   const plus=Array(n).fill(0n),minus=Array(n).fill(0n),end=Array(n).fill(0n);
   F.forEach((c,j)=>{let m=0;const b=1n<<BigInt(j);for(const l of c){const i=Math.abs(l)-1;m=Math.max(m,i);if(l>0)plus[i]|=b;else minus[i]|=b}end[m]|=b});
   let D=new Map([[0n,one]]),peak=1;
   for(let i=0;i<n;i++){const N=new Map();for(const [s,v] of D)for(const b of i<p.length?[p[i]]:[0,1]){let t=s|(b?plus[i]:minus[i]);if((t&end[i])!==end[i])continue;t&=~end[i];N.set(t,add(N.get(t)||zero,mul(v,b?w[i]:one)))}D=N;peak=Math.max(peak,D.size)}
   return {A,P:D.get(0n)||zero,inh:D.has(0n),peak};
 }
 function probe(F,n,w,p){const r=contract(F,n,w,p),D=sub(scale(r.A,3),scale(r.P,4)),u=sub(scale(r.A,3),D);ck(u.every(v=>v%4===0),"precision");return {value:u.map(v=>v/4),...r,D}}
 function extract(F,n,w,p,P){let calls=0;const x=p.slice();while(x.length<n){const v=probe(F,n,w,[...x,0]).value;calls++;if(nz(v)){x.push(0);P=v}else{x.push(1);P=res(sub(P,v))}ck(nz(P),"invariant")}ck(sat(F,x)&&eq(P,res(val(x,w))),"original witness");return {x,calls}}
 function route(n,c,p){let i=p.reduce((v,b)=>2*v+1+b,0),x=p.slice();while(x.length<n){const b=(c>>i)&1;x.push(b);i=2*i+1+b}return x}
 function locate(n,c,score,x){let l=0,r=n,calls=0;ck(!score([])&&score(x),"opposite");while(r-l>1){const m=(l+r)>>1;calls++;if(score(x.slice(0,m)))r=m;else l=m}const p=x.slice(0,l),i=p.reduce((v,b)=>2*v+1+b,0),b=(c>>i)&1;ck(b!==x[l]&&!score([...p,b])&&score([...p,1-b]),"wrong turn");return calls}
 let probes=0,comparisons=0,extracts=0,queries=0,localized=0,midpoints=0,neutral=0;
 for(let t=0;t<180;t++){const n=1+rnd(7),F=Array.from({length:rnd(11)},()=>Array.from({length:rnd(4)},()=> (rnd(2)?1:-1)*(1+rnd(n))));
  if(t%5===0)F.splice(0,F.length,...Array.from({length:1+rnd(n)},()=>[1+rnd(n)]));
  for(let k=0;k<4;k++){const w=Array.from({length:n},()=>z[rnd(31)]),p=Array.from({length:rnd(n+1)},()=>rnd(2)),ref=brute(F,n,w,p),v=probe(F,n,w,p);ck(eq(ref.A,v.A)&&eq(ref.P,v.P)&&ref.inh===v.inh&&eq(v.value,res(ref.P)),"prefix ring");comparisons++;
   if(p.length<n){const a=probe(F,n,w,[...p,0]),b=probe(F,n,w,[...p,1]);ck(eq(v.P,add(a.P,b.P))&&eq(v.D,add(a.D,b.D)),"prefix Weil split");comparisons++}
   const root=probe(F,n,w,[]);probes++;if(root.inh&&!nz(root.value))neutral++;
   if(nz(root.value)){const e=extract(F,n,w,[],root.value);extracts++;queries+=e.calls;const c=rnd(128),score=p=>sat(F,route(n,c,p));if(!score([])){midpoints+=locate(n,c,score,e.x);localized++}}
  }
 }
 // Exact source path partition and signed telescope for all n=3 truth tables and routing policies.
 let combinations=0,telescopes=0,firstPartitions=0,defectControls=0;
 for(let c=0;c<128;c++)for(let f=0;f<256;f++){
  const n=3,F=x=> (f>>x.reduce((a,b,i)=>a+(b<<i),0))&1,score=p=>F(route(n,c,p)),s0=score([]);let mass=0,part=0,delta=0;
  const regions=new Map();
  for(let u=0;u<8;u++){const x=Array.from({length:n},(_,i)=>(u>>i)&1),w=BigInt((u%3)-1),a=Array.from({length:4},(_,j)=>score(x.slice(0,j)));
   let signed=0;for(let j=0;j<n;j++)signed+=a[j+1]-a[j];ck(signed===F(x)-s0,"signed path telescope");telescopes++;delta+=Number(w)*signed;
   if(F(x)){mass+=Number(w);if(!s0){const j=a.findIndex(v=>v===1);ck(j>0&&a[j-1]===0,"first rise");const p=x.slice(0,j-1),b=x[j-1],i=p.reduce((v,b)=>2*v+1+b,0);ck(((c>>i)&1)!==b,"first defect");const key=x.slice(0,j).join("");regions.set(key,(regions.get(key)||0)+Number(w));firstPartitions++}}
  }
  ck(delta===mass-s0*Array.from({length:8},(_,u)=>(u%3)-1).reduce((a,b)=>a+b,0),"weighted telescope");
  if(!s0){ck([...regions.values()].reduce((a,b)=>a+b,0)===mass,"first rise mass");const keys=[...regions.keys()];ck(keys.every((a,i)=>keys.every((b,j)=>i===j||!b.startsWith(a))),"prefix antichain");defectControls++}combinations++;
 }
 const control=probe([],1,[one],[]),empty=probe([[]],1,[one],[]);ck(!nz(control.value)&&control.inh&&!nz(empty.value)&&!empty.inh,"zero collision");
 return {teich:31,probes,comparisons,extracts,queries,localized,midpoints,neutral,combinations,telescopes,firstPartitions,defectControls,zeroCollision:1};
}
console.log(JSON.stringify(run(),null,2));
