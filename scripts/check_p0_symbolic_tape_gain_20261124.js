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
  let cases=0,accept=0,rows=0,selectors=0,timeout=0,anchor=0,maxg=0,maxc=0,weighted=0;
  for(const n of [2,3,5])for(let kind=0;kind<3;kind++)for(const clock of [0,2,5]){
    const cs=clauses(n),tab=machine(kind);for(const l of (n===2?[0,1,2,3]:[0,2*n-1])){
      const {g,a,b,flag,lo,L}=compile(tab,clock,n,cs,l);maxg=Math.max(maxg,g.g.length);maxc=Math.max(maxc,g.cnf.length);let sums=[0,0,0], wants=[0,0,0];
      const N=n===2?256:32;
      for(let m=0;m<N;m++){const bs=cs.map((_,i)=>n===2?(m>>i)&1:rand(7)<3?1:0),rv=bs.slice();rv[l]=1;const p=direct(tab,clock,bs,n,cs),r=direct(tab,clock,rv,n,cs),val=g.lift(bs),gain=(1-p.score)*r.score;if(val[flag]!==gain||g.sat(val)!==!!gain||val[a.s]!==p.score||val[b.s]!==r.score)throw Error("score");
        for(const [c,d] of [[a,p],[b,r]]){if(c.x.some((v,i)=>val[v]!==d.x[i]))throw Error("output");for(let k=0;k<clock;k++){const row=c.rows[k],rr=d.rows[k];for(let j=0;j<L;j++){for(let q=0;q<3;q++)if(val[row.head[j][q]]!==+(j+lo===rr.h&&q===rr.q))throw Error("head");for(let s=0;s<3;s++)if(val[row.tape[j][s]]!==+((rr.tape.get(j+lo)??2)===s))throw Error("tape");selectors+=6;}rows++;}}
        if(gain){if(!cs.every((c,i)=>!bs[i]||c.some(t=>r.x[Math.abs(t)-1]===+(t>0))))throw Error("witness");accept++;}
        if(clock===0||kind===1)timeout++;if(Array.from({length:n},(_,i)=>bs[2*i]||bs[2*i+1]).every(Boolean))anchor++;
        for(let j=0;j<3;j++){const mod=[2,8,17][j];let w=1;for(let i=0;i<bs.length;i++)w=w*((i+2+bs[i])%mod)%mod;sums[j]=(sums[j]+w*val[flag])%mod;wants[j]=(wants[j]+w*gain)%mod;}cases++;}
      for(let j=0;j<3;j++){if(sums[j]!==wants[j])throw Error("mass");weighted++;}
    }}
  out.push({cases,accept,rows,selectors,timeout,anchor,maxg,maxc,weighted});return out;
}
console.log(JSON.stringify(main()));
