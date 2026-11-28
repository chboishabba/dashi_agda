// Synthetic finite controls only; no empirical or kernel acceptance.
function run() {
  const counts={joint:0,projections:0,pairwise:0,stock:0,gates:0,paths:0,horizon:0};
  function check(k,x){if(!x)throw Error(k);counts[k]++;}
  const bits=(m,n)=>Array.from({length:n},(_,i)=>(m>>i)&1);
  const all=a=>a.every(Boolean);
  for(let m=0;m<128;m++){
    const v=bits(m,7);check("joint",all(v)===(m===127));
    for(let i=0;i<7;i++)if(v[i]===1){
      const w=bits(m^(1<<i),7);
      check("projections",v.every((x,j)=>i===j||x===w[j]));
    }
  }
  // All pairwise marginals agree on even/odd 3-bit parity fibres.
  const even=[],odd=[];for(let m=0;m<8;m++){const b=bits(m,3);(b.reduce((x,y)=>x+y,0)%2?odd:even).push(b);}
  for(let i=0;i<3;i++)for(let j=i+1;j<3;j++)for(let a=0;a<2;a++)for(let b=0;b<2;b++)
    check("pairwise",even.filter(v=>v[i]===a&&v[j]===b).length===odd.filter(v=>v[i]===a&&v[j]===b).length);
  // Conservation across two locations; reserve floors are separate.
  for(let a=0;a<=6;a++)for(let b=0;b<=6;b++)for(let q=0;q<=a;q++)
    for(let c=0;c<=a-q;c++)for(let d=0;d<=b+q;d++){
      const x=a-q-c,y=b+q-d;
      check("stock",x+y+c+d===a+b&&x>=0&&y>=0);
    }
  // Exhaustive 3 actors × 3 available routes. Bit=unilateral block.
  for(let m=0;m<512;m++)for(let f=1;f<8;f++){
    const feasible=[0,1,2].filter(r=>f&(1<<r));
    const cut=a=>feasible.every(r=>m&(1<<(3*a+r)));
    const independent=[0,1,2].every(a=>feasible.some(r=>!(m&(1<<(3*a+r)))));
    check("gates",independent===![0,1,2].some(cut));
  }
  // All directed graphs on 3 vertices, 8 viable-state masks.
  for(let g=0;g<512;g++)for(let mask=0;mask<8;mask++){
    const admitted=(s,t)=>Boolean((mask&(1<<s))&&(mask&(1<<t))&&(g&(1<<(3*s+t))));
    const reach=Array.from({length:3},(_,s)=>Array.from({length:3},(_,t)=>s===t||admitted(s,t)));
    for(let k=0;k<3;k++)for(let i=0;i<3;i++)for(let j=0;j<3;j++)reach[i][j] ||= reach[i][k]&&reach[k][j];
    for(let s=0;s<3;s++)for(let m=0;m<3;m++)for(let t=0;t<3;t++)
      if((mask&(1<<s))&&reach[s][m]&&reach[m][t])
        check("paths",reach[s][t]&&Boolean(mask&(1<<t)));
  }
  for(let m=0;m<128;m++)check("horizon",all(bits(m,7))===(m===127));
  return counts;
}
console.log(JSON.stringify(run()));
