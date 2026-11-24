// Finite exact affine observer and description/time budget controls; not a universal-machine lower bound.
function main(){
  let seed=369;const rnd=n=>(seed=(Math.imul(seed,1664525)+1013904223)>>>0)%n;
  const bit=i=>1n<<BigInt(i);
  const parity=x=>{let p=0;while(x){x&=x-1n;p^=1;}return p;};
  function solve(rows,m){
    const a=rows.map(([v,b])=>[v,b]);let k=0;const piv=[];
    for(let i=0;i<m;i++){let j=k;while(j<a.length&&!(a[j][0]&bit(i)))j++;if(j===a.length)continue;[a[k],a[j]]=[a[j],a[k]];
      for(let j=0;j<a.length;j++)if(j!==k&&(a[j][0]&bit(i))){a[j][0]^=a[k][0];a[j][1]^=a[k][1];}
      piv.push(i);k++;}
    if(a.some(([v,b])=>!v&&b))return null;
    let x=0n;for(let i=0;i<k;i++)if(a[i][1])x|=bit(piv[i]);
    if(rows.some(([v,b])=>parity(v&x)!==b))throw Error("solver");
    return {x,rank:k};
  }
  function clauses(n,r,all=false){
    const out=[];function go(a,i){if(a.length===r){for(let s=0;s<2**r;s++)out.push(a.map((v,j)=>(s>>j&1)?v+1:-v-1));return;}
      for(let j=i;j<n;j++)go([...a,j],j+1);}
    if(all)for(let k=1;k<r;k++)out.push(...clauses(n,k));go([],0);return out;
  }
  const cv=(c,x)=>c.some(l=>+(!!(x&bit(Math.abs(l)-1)))===+(l>0));
  const falseMask=(cs,x)=>cs.reduce((a,c,i)=>cv(c,x)?a:a|bit(i),0n);
  const randomRow=m=>{let a=0n;for(let i=0;i<m;i++)if(rnd(17)<8)a|=bit(i);return a;};
  const sat=(cs,u,x)=>!(u&falseMask(cs,x));
  function affineFail(cs,n,L,x){
    const bx=falseMask(cs,x),m=cs.length;
    for(let y=0n;y<bit(n);y++){
      const by=falseMask(cs,y),fixed=[];
      for(let i=0;i<m;i++)if(by&bit(i))fixed.push([bit(i),0]);
      for(let i=0;i<m;i++)if((bx&~by)&bit(i)){
        const a=solve([...L,...fixed,[bit(i),1]],m);
        if(a){if(!sat(cs,a.x,y)||sat(cs,a.x,x))throw Error("affine decode");return {u:a.x,y};}
      }
    }
    return null;
  }
  const cs=clauses(2,2,true);let fibres=0,brute=0,fail=0,empty=0,neutral=0;
  for(let t=0;t<128;t++){
    const L=Array.from({length:t%10},()=>[randomRow(cs.length),rnd(7)%2]);
    for(let x=0n;x<4n;x++){
      let want=false,inhab=false,points=0;
      for(let u=0n;u<256n;u++){
        if(L.some(([a,b])=>parity(a&u)!==b))continue;
        points++;const ys=[0n,1n,2n,3n].some(y=>sat(cs,u,y));inhab ||=ys;
        want ||=ys&&!sat(cs,u,x);brute++;
      }
      const got=affineFail(cs,2,L,x);
      if(!!got!==want)throw Error("affine exact");
      if(got&&L.some(([a,b])=>parity(a&got.u)!==b))throw Error("outside fibre");
      fibres++;fail+=+want;empty+=+(points===0);neutral+=+(!want&&inhab);
    }
  }
  // Adaptive parity observer: each next query is a deterministic function of transcript.
  // At the zero transcript use restricted kernel on all x-false exact-r clauses.
  let adaptive=0,queries=0,maxM=0,nonzero=0;
  for(const n of [3,4,5,6,7,8])for(const r of [2,3])for(let rep=0;rep<12;rep++){
    const cs=clauses(n,r),m=cs.length,x=BigInt(rnd(2**n)),y=x^(bit(n)-1n),B=falseMask(cs,x);
    const indices=cs.map((_,i)=>i).filter(i=>B&bit(i));const d=indices.length;
    const q=Math.min(d-1,rep%11),pool=Array.from({length:q},()=>[randomRow(m),randomRow(m)]);
    function transcript(u){const rows=[];let state=0;for(let k=0;k<q;k++){const a=pool[k][state],b=parity(a&u);rows.push([a,b]);state^=b;}return rows;}
    const L=transcript(0n),small=L.map(([a,b])=>[indices.reduce((z,i,j)=>z|((a&bit(i))?bit(j):0n),0n),b]);
    let u=0n;
    for(let j=0;j<d;j++){const s=solve([...small,[bit(j),1]],d);if(s){u=indices.reduce((z,i,k)=>z|((s.x&bit(k))?bit(i):0n),0n);break;}}
    if(!u||u&~B||sat(cs,u,x)||!sat(cs,u,y))throw Error("kernel failure");
    const alt=transcript(u);if(alt.some(([a,b],i)=>a!==L[i][0]||b!==0))throw Error("adaptive transcript");
    adaptive++;queries+=q;maxM=Math.max(maxM,m);nonzero+=+!!u;
  }
  // Width<=2 finite line-fibre reduction: {0,u_F} with forced new z, x=0.
  let lines=0;
  for(let u=0n;u<256n;u++){
    const ext=clauses(3,2,true),encode=cs.reduce((s,c,i)=>u&bit(i)?s|bit(ext.findIndex(d=>String(d)===String(c))):s,0n)|bit(ext.findIndex(c=>String(c)==="3"));
    const satF=[0n,1n,2n,3n].some(x=>sat(cs,u,x));
    const bad=[0n,encode].some(v=>!sat(ext,v,0n)&&Array.from({length:8},(_,i)=>BigInt(i)).some(x=>sat(ext,v,x)));
    if(bad!==satF)throw Error("line reduction");lines++;
  }
  // Finite bytecode regression for universal resource budget; NOT a universal TM.
  // 4-bit opcodes, output two bits. 0 halt, 1..4 set, 5/6 toggle, 7 conditional skip,
  // 8 jump to start, remaining opcodes read input and toggle or no-op.
  function run(p,u,T){
    let pc=0,x=0;for(let t=1;t<=T;t++){if(pc<0||pc>=p.length)return null;const op=p[pc++];
      if(op===0)return {x:BigInt(x),t};
      if(op<=4)x=op-1;else if(op===5)x^=1;else if(op===6)x^=2;else if(op===7){if(!(u&1n))pc++;}else if(op===8)pc=0;else if(op<=12){if(u&bit(op-9))x^=1;}else if(op<=14){if(u&bit(op-13))x^=2;}
    }return null;
  }
  const ps=[];for(let a=0;a<16;a++){ps.push([a]);for(let b=0;b<16;b++)ps.push([a,b]);}
  let budget=0,executions=0,successes=0,misses=0,unsat=0,monotone=0,residual=0;
  const bounds=Array.from({length:12},(_,i)=>i);
  for(let u=0n;u<256n;u++){
    const inhabited=[0n,1n,2n,3n].some(x=>sat(cs,u,x));let min=Infinity;
    for(const p of ps){const a=run(p,u,127);if(a&&sat(cs,u,a.x))min=Math.min(min,4*p.length+Math.ceil(Math.log2(a.t+1)));}
    let prior=false;
    for(const b of bounds){
      let found=false;for(const p of ps){const l=4*p.length;if(l>b)continue;const a=run(p,u,2**(b-l)-1);executions++;if(a&&sat(cs,u,a.x))found=true;}
      if(found!==(min<=b)||found&&!inhabited||prior&&!found)throw Error("budget");
      budget++;successes+=+found;misses+=+(!found&&inhabited);unsat+=+!inhabited;monotone+=+(b>0);prior=found;
      if(found||inhabited&&!found){if(!inhabited)throw Error("residual");}residual++;
    }
  }
  return {fibres,brute,fail,empty,inhabitedCorrect:neutral,adaptive,queries,maxM,nonzero,lines,budget,executions,successes,misses,unsat,monotone,residual};
}
console.log(JSON.stringify(main()));
