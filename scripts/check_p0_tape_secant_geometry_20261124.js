// Exact bounded symbolic tape gain verifier; no general SAT or Clay claim.
function main(){
  const out=[];
  let seed=369;function rand(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n;}
  class C{
    constructor(m){this.m=m;this.g=[];this.cnf=[];this.cache=new Map();}
    gate(op,...a){const key=[op,...a].join(",");if(this.cache.has(key))return this.cache.get(key);const z=this.m+1+this.g.length;this.g.push([op,...a]);this.cache.set(key,z);if(op===0)this.cnf.push([-z]);else if(op===1)this.cnf.push([z]);else if(op==="!")this.cnf.push([-z,-a[0]],[z,a[0]]);else if(op==="&")this.cnf.push([-z,a[0]],[-z,a[1]],[z,-a[0],-a[1]]);else if(op==="|")this.cnf.push([z,-a[0]],[z,-a[1]],[-z,a[0],a[1]]);return z;}
    not(a){return this.gate("!",a)} and(a,b){return this.gate("&",a,b)} or(a,b){return this.gate("|",a,b)}
    all(xs){return xs.reduce((a,b)=>this.and(a,b),this.gate(1))}
    any(xs){return xs.reduce((a,b)=>this.or(a,b),this.gate(0))}
    mux(c,a,b){return this.or(this.and(c,a),this.and(this.not(c),b))}
    lift(bits){const a=[0,...bits];for(const [op,x,y] of this.g)a.push(op===0?0:op===1?1:op==="!"?1-a[x]:op==="&"?a[x]&a[y]:a[x]|a[y]);return a;}
    sat(a){return this.cnf.every(c=>c.some(l=>a[Math.abs(l)]===+(l>0)))}
  }
  function clauses(n){const cs=[];for(let i=1;i<=n;i++)cs.push([-i],[i]);for(let i=1;i<=n;i++)for(let j=i+1;j<=n;j++)for(const a of [-i,i])for(const b of [-j,j])cs.push([a,b]);return cs;}
  // Three symbols 0,1,blank=2; states 0,1,2 with 2 absorbing halt.
  function machine(kind){const t=[];for(let q=0;q<3;q++){t[q]=[];for(let a=0;a<3;a++)t[q][a]=q===2?[2,a,0]:kind===0?[q===1?2:1,a===0?1:0,q===0?1:-1]:kind===1?[q,a,1]:[rand(3),rand(3),rand(3)-1];}return t;}
  function direct(tab,clock,bs,n,cs){const tape=new Map(bs.map((b,i)=>[i,b]));let h=0,q=0;const rows=[];for(let k=0;k<clock;k++){const a=tape.get(h)??2;const [r,w,d]=tab[q][a];tape.set(h,w);q=r;h+=d;rows.push({h,q,tape:new Map(tape)});}let x=Array.from({length:n},(_,i)=>+(q===2&&tape.get(i)===1));const pinned=Array.from({length:n},(_,i)=>bs[2*i]||bs[2*i+1]).every(Boolean);if(pinned)x=Array.from({length:n},(_,i)=>bs[2*i+1]);const score=+cs.every((c,i)=>!bs[i]||c.some(l=>x[Math.abs(l)-1]===+(l>0)));return {x,score,rows};}
  function compile(tab,clock,n,cs,l){const g=new C(cs.length);const z=g.gate(0),o=g.gate(1);const orig=cs.map((_,i)=>i+1),rev=orig.map((b,i)=>i===l?o:b);const lo=-clock-1,hi=cs.length+clock;const L=hi-lo+1;
    function run(bs){let tape=Array.from({length:L},(_,j)=>{let i=j+lo;return i>=0&&i<bs.length?[g.not(bs[i]),bs[i],z]:[z,z,o]});let head=Array.from({length:L},(_,j)=>Array.from({length:3},(_,q)=>j+lo===0&&q===0?o:z));const rows=[];
      for(let k=0;k<clock;k++){const nt=[],nh=Array.from({length:L},()=>Array.from({length:3},()=>[]));for(let j=0;j<L;j++){const triggers=[];for(let q=0;q<3;q++)for(let a=0;a<3;a++){const [r,w,d]=tab[q][a],fire=g.and(head[j][q],tape[j][a]);triggers.push([fire,w]);if(j+d>=0&&j+d<L)nh[j+d][r].push(fire);}
        const stay=g.not(g.any(head[j]));nt.push(Array.from({length:3},(_,a)=>g.any([g.and(stay,tape[j][a]),...triggers.filter(t=>t[1]===a).map(t=>t[0])])));}
        head=nh.map(row=>row.map(xs=>g.any(xs)));tape=nt;rows.push({head,tape});}
      const halted=g.any(head.map(h=>h[2]));const pin=g.all(Array.from({length:n},(_,i)=>g.or(bs[2*i],bs[2*i+1])));const x=Array.from({length:n},(_,i)=>g.mux(pin,bs[2*i+1],g.and(halted,tape[i-lo][1])));const s=g.all(cs.map((c,i)=>g.or(g.not(bs[i]),g.any(c.map(l=>l>0?x[l-1]:g.not(x[-l-1]))))));return {x,s,rows};}
    const a=run(orig),b=run(rev),flag=g.and(g.not(a.s),b.s);g.cnf.push([flag]);return {g,a,b,flag,lo,L};}

  function secant(g,old,nw,endpoint){
    const d=old.map((x,i)=>nw[i]-x),adj=new Array(d.length).fill(0n);
    adj[endpoint]=1n;let active=0,changed=0;
    for(let i=g.g.length-1;i>=0;i--){
      const j=g.m+1+i,[op,x,y]=g.g[i];let a=0,b=0;
      if(op==="!")a=-1;
      if(op==="&"){a=old[y];b=nw[x];}
      if(op==="|"){a=1-old[y];b=1-nw[x];}
      if(d[j]!==a*(d[x]||0)+b*(d[y]||0))throw Error("local face");
      if(d[j])changed++;
      if(adj[j]===0n)continue;
      active++;
      if(x!==undefined)adj[x]+=adj[j]*BigInt(a);
      if(y!==undefined)adj[y]+=adj[j]*BigInt(b);
    }
    let z=0n;for(let i=1;i<=g.m;i++)z+=adj[i]*BigInt(d[i]);
    if(z!==BigInt(d[endpoint]))throw Error("global face");
    return {z,adj,changed,active};
  }
  // Exact finite repair: dirty cone is determined by actual changed gate values.
  function update(g,a,i,b,fan){
    const v=a.slice(),dirty=new Uint8Array(v.length);v[i]=b;dirty[i]=1;
    for(const j of fan[i])dirty[j]=1;
    let touched=0,changed=0;
    for(let k=0;k<g.g.length;k++){
      const j=g.m+1+k;if(!dirty[j])continue;touched++;
      const [op,x,y]=g.g[k],z=op===0?0:op===1?1:op==="!"?1-v[x]:op==="&"?v[x]&v[y]:v[x]|v[y];
      if(z!==v[j]){v[j]=z;changed++;for(const q of fan[j])dirty[q]=1;}
    }
    return {v,touched,changed};
  }
  let tests=0,faces=0,positive=0,negative=0,neutral=0,mixed=0,mixedNonzero=0,dirty=0,full=0,active=0,changed=0,verifiedGain=0;
  for(const n of [2,3,5])for(let kind=0;kind<3;kind++)for(const clock of [0,2,5]){
    const cs=clauses(n),tab=machine(kind);
    for(const l of [0,2*n-1]){
      const {g,flag}=compile(tab,clock,n,cs,l),fan=Array.from({length:g.m+1+g.g.length},()=>[]);
      for(let k=0;k<g.g.length;k++){const [op,...args]=g.g[k];for(const x of args)fan[x].push(g.m+1+k);}
      for(let m=0;m<(n===2?32:12);m++){
        const bs=cs.map((_,i)=>n===2?(m*7>>i)&1:rand(7)<3?1:0),a=g.lift(bs);
        const i=1+rand(g.m),j=1+(i+rand(g.m-1))%g.m;
        if(i===j)throw Error("not distinct");
        const bi=bs.slice();bi[i-1]^=1;const bj=bs.slice();bj[j-1]^=1;const bij=bi.slice();bij[j-1]^=1;
        const u=update(g,a,i,bi[i-1],fan),v=update(g,a,j,bj[j-1],fan),w=update(g,u.v,j,bij[j-1],fan);
        const A=g.lift(bi),B=g.lift(bj),D=g.lift(bij);
        for(const [inc,exact] of [[u,A],[v,B],[w,D]]){if(inc.v.some((x,k)=>x!==exact[k]))throw Error("incremental replay");dirty+=inc.touched;full+=g.g.length;}
        for(const [s,t] of [[a,A],[a,B],[A,D],[B,D],[a,D]]){
          const c=secant(g,s,t,flag);faces+=g.g.length;tests++;active+=c.active;changed+=c.changed;
          if(c.z>0n)positive++;else if(c.z<0n)negative++;else neutral++;
        }
        const h=D[flag]-A[flag]-B[flag]+a[flag];mixed++;if(h)mixedNonzero++;
        if((D[flag]-A[flag])-(B[flag]-a[flag])!==h)throw Error("square");
        for(const [bits,z] of [[bs,a],[bi,A],[bj,B],[bij,D]]){
          const rv=bits.slice();rv[l]=1;const p=direct(tab,clock,bits,n,cs),q=direct(tab,clock,rv,n,cs);
          if(z[flag]!==((1-p.score)*q.score))throw Error("direct endpoint");
          if(z[flag]){if(!cs.every((c,k)=>!bits[k]||c.some(t=>q.x[Math.abs(t)-1]===+(t>0))))throw Error("witness");verifiedGain++;}
        }
      }
    }
  }
  return {tests,faces,positive,negative,neutral,mixed,mixedNonzero,dirty,full,active,changed,verifiedGain};
}
console.log(JSON.stringify(main()));
