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

  const Cval=(c,x)=>c.some(l=>x[Math.abs(l)-1]===+(l>0));
  // Causal output cut; no enumeration of the unobserved source suffix.
  function contract(tab,T,n,cs,l,w,mod,pins={}){
    const k=Math.min(cs.length,Math.max(2*n,T,n)),m=cs.length,free=m-k;
    if(k>20)throw Error("cut budget");
    let z=0,ok=false,word=null,rows=0,retained=0,products=0,neutralRows=0;
    const marg=Array.from({length:m},()=>[0,0]);
    const mul=(a,b)=>{products++;return a*b%mod;};
    function pref(a){let p=[1];for(const x of a)p.push(mul(p.at(-1),x));return p;}
    function suff(a){let p=Array(a.length+1).fill(1);for(let i=a.length-1;i>=0;i--)p[i]=mul(a[i],p[i+1]);return p;}
    for(let j=0;j<2**k;j++){
      const bs=Array.from({length:m},(_,i)=>i<k?(j>>i)&1:0);
      if(Object.entries(pins).some(([i,b])=>+i<k&&bs[i]!==b))continue;
      rows++;const rv=bs.slice();rv[l]=1;
      const x=direct(tab,T,bs,n,cs).x,y=direct(tab,T,rv,n,cs).x;
      if(!Cval(cs[l],y)||cs.slice(0,k).some((c,i)=>bs[i]&&!Cval(c,y)))continue;
      retained++;const old=cs.slice(0,k).every((c,i)=>!bs[i]||Cval(c,x));
      let mass=1;for(let i=0;i<k;i++)mass=mul(mass,w[i][bs[i]]);
      const A=[],B=[],opts=[],oldOpts=[];
      for(let i=k;i<m;i++){
        const ay=Cval(cs[i],y),ax=Cval(cs[i],x);
        const a=[0,1].filter(b=>(pins[i]===undefined||pins[i]===b)&&(!b||ay));
        const b=a.filter(b=>!b||ax);
        opts.push(a);oldOpts.push(b);
        A.push(a.reduce((s,b)=>(s+w[i][b])%mod,0));B.push(b.reduce((s,b)=>(s+w[i][b])%mod,0));
      }
      const pa=pref(A),pb=pref(B),sa=suff(A),sb=suff(B);
      const v=mul(mass,(pa[free]-(old?pb[free]:0)+mod)%mod);z=(z+v)%mod;
      for(let i=0;i<k;i++)marg[i][bs[i]]=(marg[i][bs[i]]+v)%mod;
      for(let i=k;i<m;i++)for(const b of opts[i-k]){
        const t=i-k;
        const a=mul(mul(pa[t],sa[t+1]),w[i][b]);
        const c=old&&oldOpts[t].includes(b)?mul(mul(pb[t],sb[t+1]),w[i][b]):0;
        marg[i][b]=(marg[i][b]+mul(mass,(a-c+mod)%mod))%mod;
      }
      const inhabited=opts.every(a=>a.length)&&(!old||opts.some((a,i)=>a.includes(1)&&!oldOpts[i].includes(1)));
      if(inhabited){if(!v)neutralRows++;if(!ok){word=bs.slice();for(let i=k;i<m;i++)word[i]=opts[i-k][0];if(old){const t=opts.findIndex((a,i)=>a.includes(1)&&!oldOpts[i].includes(1));word[k+t]=1;}ok=true;}}
    }
    if(ok){const rv=word.slice();rv[l]=1;if(direct(tab,T,word,n,cs).score||!direct(tab,T,rv,n,cs).score||Object.entries(pins).some(([i,b])=>word[i]!==b))throw Error("cut witness");}
    for(const [a,b] of marg)if((a+b)%mod!==z)throw Error("marginal");
    return {z,marg,ok,word,rows,retained,products,neutralRows,k};
  }
  function brute(tab,T,n,cs,l,w,mod){
    let z=0,ok=false;const marg=Array.from({length:cs.length},()=>[0,0]);
    for(let mask=0;mask<2**cs.length;mask++){const bits=cs.map((_,i)=>(mask>>i)&1),rv=bits.slice();rv[l]=1;const p=direct(tab,T,bits,n,cs),q=direct(tab,T,rv,n,cs);if(p.score||!q.score)continue;ok=true;let v=1;for(let i=0;i<bits.length;i++)v=v*w[i][bits[i]]%mod;z=(z+v)%mod;for(let i=0;i<bits.length;i++)marg[i][bits[i]]=(marg[i][bits[i]]+v)%mod;}
    return {z,ok,marg};
  }
  let runs=0,bruteCases=0,marginals=0,witnesses=0,neutral=0,conditional=0,outputInvariance=0,compiled=0,rows=[];
  for(const [n,kind,T,l] of [[2,0,0,1],[2,0,2,1],[2,0,5,3],[2,1,5,3],[2,2,5,1],[3,0,0,1],[3,0,2,3],[3,1,5,5],[5,0,0,1],[5,0,2,3],[7,0,2,3]]){
    const cs=clauses(n),tab=machine(kind),m=cs.length,k=Math.min(m,Math.max(2*n,T,n));const {g,flag}=compile(tab,T,n,cs,l);
    for(let s=0;s<64;s++){const a=cs.map(()=>rand(7)<3?1:0),b=a.map((x,i)=>i<k?x:rand(7)<3?1:0);for(const force of [false,true]){if(force){a[l]=1;b[l]=1;}if(direct(tab,T,a,n,cs).x.join()!==direct(tab,T,b,n,cs).x.join())throw Error("output dependency");outputInvariance++;}}
    for(const mod of n===7?[8]:[2,8,17]){
      const w=cs.map((_,i)=>mod===2?[1,1]:[(i+2)%mod,(i*3+1)%mod]),a=contract(tab,T,n,cs,l,w,mod);runs++;marginals+=2*m;
      if(a.ok){if(!g.lift(a.word)[flag])throw Error("compiler witness");compiled++;witnesses++;if(!a.z)neutral++;}
      if(n===2||n===3&&T===0&&mod===8){const b=brute(tab,T,n,cs,l,w,mod);bruteCases+=2**m;if(a.z!==b.z||a.ok!==b.ok||JSON.stringify(a.marg)!==JSON.stringify(b.marg))throw Error("brute mismatch");}
      if(n<=5&&mod===8){for(const i of [0,m-1]){const p=contract(tab,T,n,cs,l,w,mod,{[i]:0}),q=contract(tab,T,n,cs,l,w,mod,{[i]:1});if(p.z!==a.marg[i][0]||q.z!==a.marg[i][1]||(p.ok||q.ok)!==a.ok)throw Error("pin");conditional+=2;}}
      if(mod===8)rows.push({n,kind,T,l,m,k,cutRows:a.rows,retained:a.retained,products:a.products,scalar:a.z,inhabited:a.ok,neutralRows:a.neutralRows});
    }
  }

  // Reverse-solve an actual failure using an unseen clause on the empty source.
  let forcedCases=0,forcedFailures=0,unforced=0,gainWitnesses=0,bisectCalls=0;
  for(const n of [2,3,5,7])for(let kind=0;kind<3;kind++)for(const T of [0,2,5]){
    const cs=clauses(n),tab=machine(kind),k=Math.min(cs.length,Math.max(2*n,T,n)),u=cs.map(()=>0);
    const x=direct(tab,T,u,n,cs).x;forcedCases++;
    const j=cs.findIndex((c,i)=>i>=k&&!Cval(c,x));
    if(j<0){unforced++;continue;}
    u[j]=1;const p=direct(tab,T,u,n,cs);
    if(p.score||p.x.join()!==x.join())throw Error("forced failure");
    const y=Array(n).fill(0),lit=cs[j][0];y[Math.abs(lit)-1]=+(lit>0);
    if(!Cval(cs[j],y))throw Error("constructed witness");
    const path=[u.slice()];for(let i=0;i<n;i++){const v=path.at(-1).slice();v[2*i+y[i]]=1;path.push(v);}
    const s=path.map(v=>direct(tab,T,v,n,cs).score);
    if(s[0]!==0||s[n]!==1)throw Error("anchor");
    let lo=0,hi=n,calls=0;while(hi-lo>1){const mid=(lo+hi)>>1;calls++;if(direct(tab,T,path[mid],n,cs).score)hi=mid;else lo=mid;}
    const w=direct(tab,T,path[hi],n,cs).x,ref=2*lo+y[lo];
    if(!path[lo].every((v,i)=>!v||Cval(cs[i],w))||!Cval(cs[ref],w)||s[lo]||!s[hi])throw Error("gain");
    if(calls>Math.ceil(Math.log2(n)))throw Error("budget");
    forcedFailures++;gainWitnesses++;bisectCalls+=calls;
  }
  return {runs,bruteCases,marginals,witnesses,neutral,conditional,outputInvariance,compiled,forcedCases,forcedFailures,unforced,gainWitnesses,bisectCalls,rows};
}
console.log(JSON.stringify(main()));
