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

  // Canonical Boolean DAG, original variable ids are positive; constants 0,1
  // represented by ids 0,1 and original variable i by i+1.
  class Q {
    constructor(m){this.m=m;this.nodes=[null,null,...Array(m).fill(null)];this.cache=new Map();this.cof=new Map();}
    make(op,a,b){
      if(op==="!"){if(a<2)return 1-a;if(this.nodes[a]?.[0]==="!")return this.nodes[a][1];}
      else {
        if(a>b)[a,b]=[b,a];
        if(a===b)return a;
        if(op==="&"){if(a===0)return 0;if(a===1)return b;}
        else {if(a===0)return b;if(a===1)return 1;}
        if(this.nodes[a]?.[0]==="!"&&this.nodes[a][1]===b||this.nodes[b]?.[0]==="!"&&this.nodes[b][1]===a)return op==="&"?0:1;
      }
      const k=[op,a,b].join(",");if(!this.cache.has(k)){this.cache.set(k,this.nodes.length);this.nodes.push(op==="!"?[op,a]:[op,a,b]);}return this.cache.get(k);
    }
    restrict(id,i,b){
      if(id<2)return id;if(id<=this.m+1)return id===i?b:id;
      const k=[id,i,b].join(",");if(this.cof.has(k))return this.cof.get(k);
      const [op,a,c]=this.nodes[id],v=this.make(op,this.restrict(a,i,b),op==="!"?undefined:this.restrict(c,i,b));this.cof.set(k,v);return v;
    }
  }
  function simplify(g,flag){
    const q=new Q(g.m),map=[0,...Array.from({length:g.m},(_,i)=>i+2)];
    for(const [op,a,b] of g.g)map.push(op===0?0:op===1?1:q.make(op,map[a],map[b]));
    return {q,root:map[flag]};
  }
  function frontier(q,root,order,weights,mod,cap=4096){
    let layers=[[root]],edges=[],calls=0;
    for(const i of order){
      const next=new Set(),ed=new Map();
      for(const v of layers.at(-1)){const a=q.restrict(v,i,0),b=q.restrict(v,i,1);calls+=2;ed.set(v,[a,b]);next.add(a);next.add(b);if(next.size>cap)return null;}
      layers.push([...next]);edges.push(ed);
    }
    if(layers.at(-1).some(v=>v>1))throw Error("unclosed");
    // Backward merge exact suffix truth functions, not just syntactic residuals.
    let keys=new Map(layers.at(-1).map(v=>[v,v])),peak=keys.size,sem=keys.size;const reduced=[];
    for(let k=order.length-1;k>=0;k--){
      const ids=new Map(),newkeys=new Map(),r=[];
      for(const v of layers[k]){const [a,b]=edges[k].get(v).map(z=>keys.get(z)),key=a+","+b;if(!ids.has(key)){ids.set(key,r.length);r.push([a,b]);}newkeys.set(v,ids.get(key));}
      reduced[k]=r;keys=newkeys;peak=Math.max(peak,r.length);sem+=r.length;
    }
    let back=[0,1],sup=[false,true],choice=[];
    for(let k=order.length-1;k>=0;k--){const w=weights[order[k]-2],r=reduced[k];choice[k]=r.map(([a,b])=>sup[a]?0:sup[b]?1:-1);const next=r.map(([a,b])=>(w[0]*back[a]+w[1]*back[b])%mod);sup=r.map(([a,b])=>sup[a]||sup[b]);back=next;}
    const bit=Array(q.m).fill(0);let v=keys.get(root);
    const z=back[v],ok=sup[v];if(ok)for(let k=0;k<order.length;k++){const b=choice[k][v];if(b<0)throw Error("lost witness");bit[order[k]-2]=b;v=reduced[k][v][b];}
    return {z,ok,bit,peak,sem,raw:layers.reduce((a,x)=>a+x.length,0),rawPeak:Math.max(...layers.map(x=>x.length)),calls,cof:q.cof.size};
  }
  function factors(q,root,w,mod,cap=14){
    const fs=[],ids=new Set(),seen=new Set();
    const put=(scope,fn)=>{scope=[...new Set(scope)].sort((a,b)=>a-b);const v=[],s=[];for(let mask=0;mask<2**scope.length;mask++){const get=i=>i<2?i:(mask>>scope.indexOf(i))&1;const [a,b]=fn(get);v.push(a);s.push(b);}fs.push({scope,v,s});scope.forEach(i=>ids.add(i));};
    function visit(id){if(id<2||id<=q.m+1||seen.has(id))return;seen.add(id);const [op,a,b]=q.nodes[id];visit(a);if(b!==undefined)visit(b);put([id,a,...(b===undefined?[]:[b])].filter(i=>i>=2),get=>{const x=get(a),y=b===undefined?0:get(b),ok=get(id)===(op==="!"?1-x:op==="&"?x&y:x|y);return [+ok,ok];});}
    visit(root);put(root<2?[]:[root],get=>[get(root),!!get(root)]);
    for(let i=2;i<=q.m+1;i++)put([i],get=>[w[i-2][get(i)],true]);
    const trace=[];let max=0,cells=0,checks=0,initial=fs.length;
    while(ids.size){
      const adj=new Map([...ids].map(i=>[i,new Set()]));
      for(const f of fs)for(const i of f.scope)for(const j of f.scope)if(i!==j)adj.get(i).add(j);
      let best,rank;
      for(const [i,ns] of adj){let fill=0;const a=[...ns];for(let j=0;j<a.length;j++)for(let k=j+1;k<a.length;k++){checks++;if(!adj.get(a[j]).has(a[k]))fill++;}const r=[fill,a.length,i];if(!rank||r[0]<rank[0]||r[0]===rank[0]&&(r[1]<rank[1]||r[1]===rank[1]&&r[2]<rank[2])){best=i;rank=r;}}
      const picked=fs.filter(f=>f.scope.includes(best));for(let j=fs.length-1;j>=0;j--)if(fs[j].scope.includes(best))fs.splice(j,1);
      const scope=[...new Set(picked.flatMap(f=>f.scope))].filter(i=>i!==best).sort((a,b)=>a-b);
      max=Math.max(max,scope.length+1);if(max>cap)return null;
      const v=[],s=[],choice=[];
      for(let mask=0;mask<2**scope.length;mask++){let sum=0,ok=false,chosen=-1;for(let b=0;b<2;b++){let p=1,sp=true;for(const f of picked){let j=0;for(let k=0;k<f.scope.length;k++){const i=f.scope[k];j|=(i===best?b:(mask>>scope.indexOf(i))&1)<<k;}p=p*f.v[j]%mod;sp=sp&&f.s[j];cells++;}sum=(sum+p)%mod;if(sp){ok=true;if(chosen<0)chosen=b;}}v.push(sum);s.push(ok);choice.push(chosen);}
      trace.push({best,scope,choice});fs.push({scope,v,s});ids.delete(best);
    }
    const z=fs.reduce((a,f)=>a*f.v[0]%mod,1),ok=fs.every(f=>f.s[0]),a=new Map();
    if(ok)for(const t of trace.reverse()){const m=t.scope.reduce((m,i,k)=>m|a.get(i)<<k,0),b=t.choice[m];if(b<0)throw Error("factor witness");a.set(t.best,b);}
    return {z,ok,bit:Array.from({length:q.m},(_,i)=>a.get(i+2)),max,cells,checks,initial,live:seen.size};
  }
  let graphs=0,comp=0,witness=0,zero=0,brute=0,pinned=0,capStops=0,rows=[];
  for(const [n,kind,clock,l] of [[2,0,0,1],[2,0,2,1],[2,0,5,3],[2,1,5,3],[2,2,5,1],[3,0,0,1],[3,0,2,3],[3,1,5,5],[5,0,0,1],[5,0,2,3]]){
    const cs=clauses(n),tab=machine(kind),{g,flag}=compile(tab,clock,n,cs,l),{q,root}=simplify(g,flag),initialNodes=q.nodes.length,order=Array.from({length:g.m},(_,i)=>i+2);
    let line={n,kind,clock,l,gates:g.g.length,sourceBits:g.m};
    for(let rep=0;rep<3;rep++){
      const mod=[2,8,17][rep],w=order.map((_,i)=>rep===0?[1,1]:[(i+2)%mod,(i*3+1)%mod]);
      const a=factors(q,root,w,mod),b=frontier(q,root,order,w,mod),c=frontier(q,root,order.slice().reverse(),w,mod);
      if(!a||!b||!c){capStops++;line.cap=true;continue;}
      if(a.z!==b.z||b.z!==c.z||a.ok!==b.ok||b.ok!==c.ok)throw Error("geometry mismatch");
      comp++;
      if(a.ok){for(const t of [a,b,c]){const bits=t.bit,rv=bits.slice();rv[l]=1;const p=direct(tab,clock,bits,n,cs),s=direct(tab,clock,rv,n,cs);if(p.score||!s.score||!g.lift(bits)[flag])throw Error("decoded witness");witness++;}if(a.z===0)zero++;}
      if(n===2){let z=0,ok=false;for(let m=0;m<256;m++){const bits=order.map((_,i)=>(m>>i)&1),rv=bits.slice();rv[l]=1;const p=direct(tab,clock,bits,n,cs),s=direct(tab,clock,rv,n,cs),v=(1-p.score)*s.score;let weight=1;for(let k=0;k<bits.length;k++)weight=weight*w[k][bits[k]]%mod;z=(z+v*weight)%mod;ok=ok||!!v;brute++;}if(z!==a.z||ok!==a.ok)throw Error("brute");}
      if(rep===1){
        // Pin using separate weight zeroing plus independent support graph restriction.
        const i=order[0],roots=[q.restrict(root,i,0),q.restrict(root,i,1)];
        const p=roots.map((v,b)=>{const ww=w.map(x=>x.slice());ww[0]=b?[0,w[0][1]]:[w[0][0],0];return factors(q,v,ww,mod);});
        if(p.every(Boolean)){if((p[0].z+p[1].z)%mod!==a.z)throw Error("pin partition");pinned++;}
      }
      Object.assign(line,{bag:a.max,entries:a.cells,discovery:a.checks,live:a.live,forward:b.peak,reverse:c.peak,rawForward:b.raw,rawReverse:c.raw,cofactors:q.cof.size,initialNodes});
    }
    rows.push(line);graphs++;
  }
  return {graphs,comp,witness,zero,brute,pinned,capStops,rows};
}
console.log(JSON.stringify(main()));
