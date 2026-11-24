// Exact finite signed consumer obstruction: Z/(2^H), source gain control.
function run(){
 const ck=(v,m)=>{if(!v)throw Error(m)};
 let seed=131;const rnd=n=>{seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return (seed>>>0)%n};
 const mod=(a,m)=>(a%m+m)%m;
 const val=(a,m)=>{if(!a)return 999;let k=0;while(a%2===0){a/=2;k++}return k};
 const dot=(a,b,m)=>mod(a.reduce((s,v,i)=>s+v*b[i],0),m);
 const step=(a,T,m)=>T[0].map((_,j)=>dot(a,T.map(r=>r[j]),m));
 function contains(rows,target,m){
  const A=rows.map(r=>r.slice()),t=target.slice();let pos=0;
  for(let j=0;j<t.length;j++){
   let p=-1;for(let i=pos;i<A.length;i++)if(A[i][j]&&(p<0||val(A[i][j],m)<val(A[p][j],m)))p=i;
   if(p<0){if(t[j])return false;continue}
   [A[p],A[pos]]=[A[pos],A[p]];const r=A[pos],g=2**val(r[j],m);
   let inv=1;while(mod(inv*(r[j]/g),m/g)!==1%(m/g))inv++;
   if(t[j]%g)return false;const z=mod(t[j]/g*inv,m/g);
   for(let k=j;k<t.length;k++)t[k]=mod(t[k]-z*r[k],m);
   for(let i=pos+1;i<A.length;i++){const z=mod(A[i][j]/g*inv,m/g);for(let k=j;k<t.length;k++)A[i][k]=mod(A[i][k]-z*r[k],m)}
   // retain annihilator multiple of pivot as a generator for tail (nonunit pivot).
   const ann=r.map(x=>mod(x*(m/g),m));if(ann.some(Boolean))A.push(ann);
   pos++;
  }return !t.some(Boolean);
 }
 function find(u,Ts,v,m){
  const rows=[],queue=[];let expanded=0;
  const add=(r,w)=>{if(!contains(rows,r,m)){rows.push(r);queue.push([r,w])}};
  add(u,"");
  for(let i=0;i<queue.length;i++){const [r,w]=queue[i];expanded++;if(dot(r,v,m))return {w,rows:rows.length,expanded};Ts.forEach((T,a)=>add(step(r,T,m),w+a))}
  return {w:null,rows:rows.length,expanded};
 }
 function brute(u,Ts,v,m){const seen=new Set([u.join()]),queue=[[u,""]];for(let i=0;i<queue.length;i++){const [r,w]=queue[i];if(dot(r,v,m))return w;Ts.forEach((T,a)=>{const x=step(r,T,m);if(!seen.has(x.join())){seen.add(x.join());queue.push([x,w+a])}})}return null}
 let membership=0,search=0,zero=0,nonzero=0,maxRows=0,delays=0;
 for(const m of [2,4,8])for(let d=1;d<=3;d++)for(let z=0;z<120;z++){
  const row=()=>Array.from({length:d},()=>rnd(m)),rows=Array.from({length:rnd(5)},row),t=row();let S=new Map([[Array(d).fill(0).join(),Array(d).fill(0)]]);
  for(const r of rows){const N=new Map();for(const x of S.values())for(let k=0;k<m;k++){const y=x.map((a,j)=>mod(a+k*r[j],m));N.set(y.join(),y)}S=N}
  ck(contains(rows,t,m)===S.has(t.join()),"membership");membership++;
  const u=row(),v=row(),Ts=[Array.from({length:d},row),Array.from({length:d},row)];
  const a=find(u,Ts,v,m),b=brute(u,Ts,v,m);ck((a.w===null)===(b===null),"nonzero test");ck(a.rows<=Math.log2(m)*d,"module length");
  if(a.w!==null){let r=u;for(const c of a.w)r=step(r,Ts[+c],m);ck(dot(r,v,m)!==0&&a.w.length<=Math.log2(m)*d-1,"witness bound");nonzero++}else zero++;
  maxRows=Math.max(maxRows,a.rows);search++;
 }
 // Exact delayed unary language: shift down a chain, terminal state loops.
 for(let d=1;d<=32;d++){const u=Array.from({length:d},(_,i)=>+(i===0)),v=Array.from({length:d},(_,i)=>+(i===d-1)),T=Array.from({length:d},(_,i)=>Array.from({length:d},(_,j)=>+(j===Math.min(i+1,d-1))));const a=find(u,[T],v,2);ck(a.w.length===d-1,"sharp");delays++}
 // Actual ordinary CNF syntax control: repeated A/B clauses, unit x1 gain iff m=n.
 const evalF=(F,x)=>F.every(c=>c.some(l=>x[Math.abs(l)-1]===+(l>0)));
 function W(F){if(F.some(c=>c.length===1&&c[0]===1))return [1,0];let a=0,b=0;for(const c of F){if(c.join()==="1,2")a++;else if(c.join()==="1,-2")b++;else return [0,0]}return a===b?[0,0]:[1,0]}
 let gains=0,source=0;
 for(let a=1;a<=48;a++)for(let b=1;b<=48;b++){const F=[...Array.from({length:a},()=>[1,2]),...Array.from({length:b},()=>[1,-2])],Fp=[...F,[1]],g=+(!evalF(F,W(F))&&evalF(Fp,W(Fp)));ck(g===+(a===b),"source equality gain");if(g)gains++;source++}
 return {membership,search,zero,nonzero,maxRows,delays,source,gains};
}
console.log(JSON.stringify(run(),null,2));
