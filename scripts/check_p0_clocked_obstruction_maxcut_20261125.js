// Finite source-patch and syntactic quotation controls. Does not execute exponential clocks or prove a Clay separation.
function main(){
  // Original two-variable source universe: four unit and four binary clauses.
  const clauses=[[-1],[1],[-2],[2],[-1,-2],[-1,2],[1,-2],[1,2]];
  function sat(u,x){return clauses.every((c,i)=>!(u&(1<<i))||c.some(l=>((x>>(Math.abs(l)-1))&1)===+(l>0)));}
  function W0(u){return ((u>>1)&1)|(((u>>3)&1)<<1);}
  function refine(u,l){return u|(1<<l);}
  function score(W,u){return +sat(u,W(u));}
  function gain(W,u,l){return (1-score(W,u))*score(W,refine(u,l));}
  function patch(parent,l){
    const y=W0(refine(parent,l));
    return u=>u===parent&&sat(parent,y)?y:W0(u);
  }
  let pairs=0,initial=0,eliminated=0,stillIncomplete=0,anchored=0,actualWitness=0;
  for(let u=0;u<256;u++)for(let l=0;l<4;l++){
    const W=patch(u,l);pairs++;const g=gain(W0,u,l);initial+=g;
    if(gain(W,u,l))throw Error("self-repair failed");
    eliminated+=g;
    let other=false;
    for(let v=0;v<256;v++){
      const allPins=!!(v&3)&&!!(v&12);
      if(allPins){const truth=[0,1,2,3].some(x=>sat(v,x));if(!!score(W,v)!==truth)throw Error("anchor");anchored++;}
      for(let j=0;j<4;j++)if(gain(W,v,j)){other=true;const y=W(refine(v,j));if(!sat(v,y)||!sat(refine(v,j),y))throw Error("witness");actualWitness++;}
    }
    if(!other)throw Error("finite fallback no longer incomplete");
    stillIncomplete++;
  }
  // The syntactic fixed point: specialize a fixed template with its own
  // literal source and k.  No execution of the finder is needed to build e.
  function template(q,k,oracleText){
    const program="("+q+")("+JSON.stringify(q)+","+JSON.stringify(k)+","+JSON.stringify(oracleText)+")";
    const e=JSON.stringify({program,coefficient:"1"+"0".repeat(k),degree:4});
    const find=JSON.parse(oracleText);
    // Mock finder returns a pair and records the exact description it was given.
    // Its input is the entire clocked descriptor, not a program without clock.
    const chosen=find[(JSON.parse(e).program.length+ k)%find.length];
    const [u,l]=chosen,cs=[[-1],[1],[-2],[2],[-1,-2],[-1,2],[1,-2],[1,2]];
    const verify=(v,x)=>cs.every((c,i)=>!(v&(1<<i))||c.some(a=>((x>>(Math.abs(a)-1))&1)===+(a>0)));
    const fallback=v=>((v>>1)&1)|(((v>>3)&1)<<1);
    const revised=u|(1<<l),y=fallback(revised);
    const W=v=>v===u&&verify(u,y)?y:fallback(v);
    return {e,chosen,scoreParent:verify(u,W(u)),scoreChild:verify(revised,W(revised))};
  }
  const genuine=[];for(let u=0;u<256;u++)for(let l=0;l<4;l++)if(gain(W0,u,l))genuine.push([u,l]);
  let quote=0;
  for(const k of [8,16,32,64,128,256]){
    const q=template.toString(),d=JSON.stringify(genuine);
    const program="("+q+")("+JSON.stringify(q)+","+JSON.stringify(k)+","+JSON.stringify(d)+")";
    const e=JSON.stringify({program,coefficient:"1"+"0".repeat(k),degree:4});
    const r=new Function("return "+program)();
    if(r.e!==e||!genuine.some(a=>a.join()===r.chosen.join())||!r.scoreParent&&r.scoreChild)throw Error("quote or patch");
    quote++;
  }
  // Fixed-source classifier control: finite short domain, fallback outside.
  // Simulated decider output is an independent bit; no claim to execute a
  // general EXPTIME or 2-EXPTIME machine in this regression.
  const exact=u=>[0,1,2,3].find(x=>sat(u,x))??W0(u);
  let classifier=0;
  for(const bit of [0,1]){
    const W=bit?W0:exact;
    const observed=Array.from({length:256},(_,u)=>u).some(u=>[0,1,2,3].some(l=>gain(W,u,l)));
    if(observed!==!!bit)throw Error("classifier");
    classifier++;
  }
  return {pairs,initial,eliminated,stillIncomplete,anchored,actualWitness,quote,classifier};
}
console.log(JSON.stringify(main()));
