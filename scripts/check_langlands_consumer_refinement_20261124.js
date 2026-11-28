// Exact standalone Langlands R157–R163 regression. Run with node.
function run() {
  let seed=157; const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n};
  const check=(x,msg)=>{if(!x)throw Error(msg)};
  const add=(m,key,w,wit)=>{if(m.has(key))m.get(key).w+=w;else m.set(key,{w,wit})};
  const bit=(i)=>1n<<BigInt(i);
  const evalCNF=(cs,x)=>cs.every(c=>c.some(([i,v])=>Number((x>>BigInt(i))&1n)===v));
  function packet(n,cs,weights,sy,a,d) {
    const groups=new Map();
    for(let i=0;i<n;i++){
      let p=0n,m=0n;
      cs.forEach((c,j)=>c.forEach(([v,b])=>{if(v===i){if(b)p|=bit(j);else m|=bit(j)}}));
      const key=`${p},${m}`;
      if(!groups.has(key))groups.set(key,{p,m,ids:[]});
      groups.get(key).ids.push(i);
    }
    const gs=[...groups.values()],last=Array(cs.length).fill(-1);
    gs.forEach((g,t)=>cs.forEach((_,j)=>{if((g.p|g.m)&bit(j))last[j]=t}));
    if(last.includes(-1))return {D:new Map(),groups:gs.length,peak:0};
    let D=new Map([["0,0,0,0",{w:1n,wit:0n}]]),peak=1;
    for(let t=0;t<gs.length;t++){
      const g=gs[t];let L=new Map([["0,0,0,0",{w:1n,wit:0n}]]);
      for(const i of g.ids){
        const N=new Map();
        for(const [key,e] of L){const [f,s,h,r]=key.split(",").map(Number);
          for(let b=0;b<2;b++)add(N,`${f|(b?2:1)},${s^(b?sy[i]:0)},${Math.min(a,h+b)},${(r+b)%d}`,e.w*weights[i][b],e.wit|(b?bit(i):0n));
        }L=N;
      }
      let end=0n;last.forEach((x,j)=>{if(x===t)end|=bit(j)});
      const N=new Map();
      for(const [key,e] of D){const [u,ss,hh,rr]=key.split(",");const s=+ss,h=+hh,r=+rr;
        for(const [lk,l] of L){const [f,v,j,k]=lk.split(",").map(Number);
          let sat=BigInt(u)|((f&2)?g.p:0n)|((f&1)?g.m:0n);
          if((sat&end)!==end)continue;
          sat&=~end;
          add(N,`${sat},${s^v},${Math.min(a,h+j)},${(r+k)%d}`,e.w*l.w,e.wit|l.wit);
        }
      }D=N;peak=Math.max(peak,D.size);
    }
    return {D,groups:gs.length,peak};
  }
  function brute(n,cs,w,sy,a,d){
    const D=new Map();
    for(let x=0n;x<bit(n);x++){if(!evalCNF(cs,x))continue;let s=0,h=0,p=1n;
      for(let i=0;i<n;i++){const b=Number((x>>BigInt(i))&1n);if(b){s^=sy[i];h++}p*=w[i][b]}
      add(D,`0,${s},${Math.min(a,h)},${h%d}`,p,x);
    }return D;
  }
  let packetTests=0,witnessTests=0,modTests=0;
  for(let t=0;t<240;t++){
    const n=1+rnd(9),cs=Array.from({length:rnd(10)},()=>Array.from({length:rnd(5)},()=>[rnd(n),rnd(2)]));
    const w=Array.from({length:n},()=>[BigInt(rnd(7)-3),BigInt(rnd(7)-3)]),sy=Array.from({length:n},()=>rnd(4)),a=rnd(n+2),d=1+rnd(5);
    const A=packet(n,cs,w,sy,a,d).D,B=brute(n,cs,w,sy,a,d);
    check(A.size===B.size,"support size");
    for(const [key,e] of A){check(B.has(key)&&B.get(key).w===e.w,"weighted packet");check(evalCNF(cs,e.wit),"witness source");let s=0,h=0;for(let i=0;i<n;i++)if(e.wit&bit(i)){s^=sy[i];h++}check(key===`0,${s},${Math.min(a,h)},${h%d}`,"witness signature");witnessTests++}
    packetTests++;
    for(const p of [2n,4n,8n,9n,25n]){
      const mw=w.map(v=>v.map(z=>(z%p+p)%p)),C=packet(n,cs,mw,sy,a,d).D;check(C.size===B.size,"mod support");
      for(const [key,e] of C)check((e.w-B.get(key).w)%p===0n,"mod packet");modTests++;
    }
  }
  function cycle(g,n){return Array.from({length:g},(_,j)=>[...Array.from({length:n},(_,i)=>[j*n+i,1]),...Array.from({length:n},(_,i)=>[((j+1)%g)*n+i,0])]);}
  let cycleTests=0;
  for(let g=3;g<=4;g++)for(let n=1;n<=2;n++){
    const q=g*n,cs=cycle(g,n),w=Array.from({length:q},()=>[1n,1n]),sy=Array.from({length:q},(_,i)=>i%2);
    const A=packet(q,cs,w,sy,3,3).D,B=brute(q,cs,w,sy,3,3);
    check(A.size===B.size&&[...A].every(([k,e])=>B.get(k)?.w===e.w),"cycle exact");cycleTests++;
  }
  const large=[];
  for(const [g,n] of [[12,8],[24,8],[48,8]]){
    const q=g*n,cs=cycle(g,n),w=Array.from({length:q},()=>[1n,1n]),sy=Array.from({length:q},(_,i)=>i%2);
    const A=packet(q,cs,w,sy,3,3);
    // A cyclic implication between all-zero/all-one group categories:
    // forbid (all-zero,all-one) across consecutive blocks. Independent 3x3 transfer trace.
    const counts=[1n,1n,bit(n)-2n];let T=Array.from({length:3},(_,i)=>Array.from({length:3},(_,j)=>i===0&&j===1?0n:counts[j]));
    const mul=(A,B)=>A.map(r=>B[0].map((_,j)=>r.reduce((s,v,k)=>s+v*B[k][j],0n)));
    let P=Array.from({length:3},(_,i)=>Array.from({length:3},(_,j)=>i===j?1n:0n));
    for(let i=0;i<g;i++)P=mul(P,T);
    const total=P.reduce((s,r,i)=>s+r[i],0n);
    check([...A.D.values()].reduce((s,e)=>s+e.w,0n)===total,"cyclic trace");
    check(A.groups===g,"discovery");large.push({groups:g,guards:q,peak:A.peak,terminal:A.D.size,total:total.toString()});
  }
  // Exact linear refinement telescope on integer modules, coarse projection
  // C sums coordinates 0,1 and keeps 2; J chooses representative 0.
  const dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0n), mv=(A,x)=>A.map(r=>dot(r,x));
  const tr=A=>A[0].map((_,j)=>A.map(r=>r[j]));
  const sub=(a,b)=>a.map((x,i)=>x-b[i]);
  const C=[[1n,1n,0n],[0n,0n,1n]],J=[[1n,0n],[0n,0n],[0n,1n]];
  const mm=(A,B)=>A.map(r=>tr(B).map(c=>dot(r,c)));
  let telescopeTests=0,modTelescope=0;
  for(let t=0;t<200;t++){
    const rand=()=>BigInt(rnd(9)-4),N=1+rnd(6),Ts=Array.from({length:N},()=>Array.from({length:3},()=>Array.from({length:3},rand))),v=Array.from({length:3},rand),f=Array.from({length:3},rand),g=Array.from({length:2},rand);
    const U=Ts.map(T=>mm(mm(C,T),J)),adj=Array(N+1);adj[N]=g;for(let i=N-1;i>=0;i--)adj[i]=mv(tr(U[i]),adj[i+1]);
    let x=v,y=mv(C,v),res=0n;
    for(let i=0;i<N;i++){const xx=mv(Ts[i],x),def=sub(mv(C,xx),mv(U[i],mv(C,x)));res+=dot(adj[i+1],def);x=xx;y=mv(U[i],y)}
    res+=dot(sub(f,mv(tr(C),g)),x);
    check(dot(f,x)-dot(g,y)===res,"telescope");telescopeTests++;
    for(const p of [2n,4n,8n,9n,25n]){check((dot(f,x)-dot(g,y)-res)%p===0n,"mod telescope");modTelescope++}
  }
  // Actual source suffix clause x OR y with y=0: dropping the x-prefix
  // satisfied bit identifies two source histories with distinct outcomes.
  check(evalCNF([[[0,1],[1,1]]],0n)===false&&evalCNF([[[0,1],[1,1]]],1n)===true,"actual suffix collision");
  return {packetTests,witnessTests,modTests,cycleTests,large,telescopeTests,modTelescope,sourceCollision:1};
}
console.log(JSON.stringify(run(), null, 2));
