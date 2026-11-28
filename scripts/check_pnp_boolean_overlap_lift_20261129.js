// Section 44: adaptive overlap conditioning and exact finite referee.
// Run: node scripts/check_pnp_boolean_overlap_lift_20261129.js
// No dependencies; GF(p) finite controls with small primes and bit masks.
function campaign() {
  "use strict";
  // Exact finite field arithmetic. Bit masks index variables; campaign cap n<=20.
  const assert=(b,m)=>{if(!b)throw Error(m)};
  const bits=m=>{let a=[];for(let i=0;m;i++,m>>>=1)if(m&1)a.push(i);return a};
  const pop=m=>bits(m).length;
  const subsets=m=>{let a=[];for(let t=m;;t=(t-1)&m){a.push(t);if(t===0)return a}};
  const mod=(x,p)=>(x%p+p)%p;
  function build(n,p) {
    let g=[], supports=[];
    const add=(op,a,b)=>{
      let s=op==="v"?1<<a:op==="c"?0:supports[a]|supports[b];
      g.push([op,a,b]);supports.push(s);return g.length-1;
    };
    const v=Array.from({length:n},(_,i)=>add("v",i));
    const z=add("c",0),o=add("c",1);
    return {n,p,g,supports,add,v,z,o};
  }
  function overlap(C,r) {
    let seen=new Set(),W=0,t=0,stack=[r];
    while(stack.length){let i=stack.pop();if(seen.has(i))continue;seen.add(i);
      let [op,a,b]=C.g[i];if(op==="+"||op==="*"){stack.push(a,b);if(op==="*"){let s=C.supports[a]&C.supports[b];W|=s;t=Math.max(t,pop(s))}}
    }return {W,t,reachable:seen.size};
  }
  function lift(C,r) {
    let D=build(C.n,C.p),cache=new Map(),calls=0,branches=0,maxContexts=0,maxLocal=0,maxAssigned=0;
    let byGate=new Map(),selectors=new Map(),overlapChecks=0;
    const plus=(a,b)=>D.add("+",a,b);
    const times=(a,b)=>{assert(!(D.supports[a]&D.supports[b]),"nonmultilinear output gate");overlapChecks++;return D.add("*",a,b)};
    function selector(K,A) {
      let key=K+":"+A;if(selectors.has(key))return selectors.get(key);
      let s=D.o;
      for(let i of bits(K)){let x=D.v[i];if(!(A&(1<<i)))x=plus(D.o,times(D.add("c",C.p-1),x));s=times(s,x)}
      selectors.set(key,s);return s;
    }
    function rec(i,K,A) {
      K&=C.supports[i];A&=K;
      const key=i+":"+K+":"+A;
      if(cache.has(key))return cache.get(key);
      calls++;byGate.set(i,(byGate.get(i)||0)+1);maxContexts=Math.max(maxContexts,byGate.get(i));maxAssigned=Math.max(maxAssigned,pop(K));
      let [op,a,b]=C.g[i],out;
      if(op==="c")out=D.add("c",a);
      else if(op==="v")out=(K&(1<<a))?((A&(1<<a))?D.o:D.z):D.v[a];
      else if(op==="+")out=plus(rec(a,K,A),rec(b,K,A));
      else {
        let S=(C.supports[a]&C.supports[b])&~K;
        maxLocal=Math.max(maxLocal,pop(S));out=D.z;
        for(let T of subsets(S)){
          branches++;
          let left=rec(a,K|S,A|T),right=rec(b,K|S,A|T);
          out=plus(out,times(times(left,right),selector(S,T)));
        }
      }
      assert(!(D.supports[out]&K),"conditioned variable escaped");
      cache.set(key,out);return out;
    }
    let root=rec(r,0,0);
    return {D,root,ledger:{states:calls,branches,maxContexts,maxLocal,maxAssigned,overlapChecks,outputGates:D.g.length}};
  }
  function evals(C,assignment){
    let v=[];for(let [op,a,b] of C.g){
      v.push(op==="v"?(assignment>>a)&1:op==="c"?mod(a,C.p):mod(op==="+"?v[a]+v[b]:v[a]*v[b],C.p))
    }return v;
  }
  function mobius(values,n,p){
    let a=values.slice();for(let i=0;i<n;i++)for(let m=0;m<a.length;m++)if(m&(1<<i))a[m]=mod(a[m]-a[m^(1<<i)],p);return a;
  }
  // Independent coefficient oracle; formal route rejects repeated supports;
  // quotient route computes union products and exact degree truncation.
  function coefficients(C,r,d,formal) {
    let rows=[];
    const put=(M,k,v)=>{v=mod((M.get(k)||0)+v,C.p);if(v)M.set(k,v);else M.delete(k)};
    for(let [op,a,b] of C.g){
      let M=new Map();
      if(op==="c")put(M,0,a);
      else if(op==="v"){if(d>=1)put(M,1<<a,1)}
      else if(op==="+"){for(let j of [a,b])for(let [k,v] of rows[j])put(M,k,v)}
      else for(let [u,x] of rows[a])for(let [v,y] of rows[b]){
        assert(!formal||!(u&v),"formal overlap");if(pop(u|v)<=d)put(M,u|v,x*y);
      }
      rows.push(M);
    }return rows[r];
  }
  let counts={circuits:0,cubePoints:0,coefficients:0,degreeComparisons:0,productDisjointChecks:0};
  let seed=4401;const rnd=k=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%k};
  function verify(C,r) {
    let {D,root,ledger}=lift(C,r),o=overlap(C,r),vals=[];
    for(let x=0;x<1<<C.n;x++){
      let v=evals(C,x)[r];assert(v===evals(D,x)[root],"cube mismatch");vals.push(v);counts.cubePoints++;
    }
    const ref=mobius(vals,C.n,C.p),out=coefficients(D,root,C.n,true);
    for(let m=0;m<ref.length;m++){assert((out.get(m)||0)===ref[m],"formal coefficient mismatch");counts.coefficients++}
    for(let d=0;d<=C.n;d++){let got=coefficients(C,r,d,false);
      for(let m=0;m<ref.length;m++){assert((got.get(m)||0)===(pop(m)<=d?ref[m]:0),"truncation mismatch");counts.degreeComparisons++}}
    counts.circuits++;counts.productDisjointChecks+=ledger.overlapChecks;
    return {...o,globalWidth:pop(o.W),inputGates:C.g.length,...ledger};
  }
  for(let p of [2,3,5,7])for(let n=1;n<=6;n++)for(let trial=0;trial<15;trial++){
    let C=build(n,p);
    for(let j=0;j<24;j++){let a=rnd(C.g.length),b=rnd(C.g.length);C.add(rnd(2)?"*":"+",a,b)}
    verify(C,C.g.length-1);
  }
  // Adversarial local-vs-global width: independent repeated variables.
  let independent=[];
  for(let n of [2,4,8,16]){
    let C=build(n,2);let r=C.o;for(let x of C.v)r=C.add("*",r,C.add("*",x,x));
    let L=lift(C,r),o=overlap(C,r);
    assert(o.t===1&&pop(o.W)===n,"bad local/global fixture");
    let f=coefficients(L.D,L.root,n,true);assert(f.size===1&&f.get((1<<n)-1)===1,"independent lift mismatch");
    independent.push({n,t:o.t,w:pop(o.W),globalBranches:2**n,...L.ledger});
  }
  // Repeated squaring: unrolled formal parse leaf count doubles at each step.
  let squaring=[];
  for(let depth of [1,4,8,16,32]){
    let C=build(1,2),r=C.v[0];
    for(let i=0;i<depth;i++)r=C.add("*",r,r);
    let L=verify(C,r);squaring.push({depth,formalParseLeaves:String(2**depth),...L});
  }
  // Explicit failure of the unmodified E.4 product recurrence in quotient:
  // (x+y)(x+z) has degree-one coefficient x although neither disjoint split does.
  let C=build(3,2),a=C.add("+",C.v[0],C.v[1]),b=C.add("+",C.v[0],C.v[2]),r=C.add("*",a,b);
  assert(coefficients(C,r,1,false).get(1)===1,"overlap counterexample");
  verify(C,r);
  // Consumer firewall: independent binary choices, OR existence vs parity.
  let consumer=[];
  for(let n=1;n<=12;n++){let count=2**n;assert(count>0&&count%2===0,"consumer counterexample");consumer.push({n,count,sat:1,parity:0})}
  return {status:"PASS",seed:4401,counts,independent,squaring,consumer,scope:"finite exact checks; not an upstream Lean build or Clay theorem"};
}
console.log(JSON.stringify(campaign(),null,2));
