// Synthetic finite regression; no runtime trade, authority or empirical acceptance.
function run(){
 const counts={selection:0,scenario:0,baseline:0,realization:0};
 function ck(k,v){if(!v)throw Error(k);counts[k]++}
 // Toy model: 2 scenarios × 2 non-substitutable benefit coordinates.
 // Each delta can be -1,0,+1; no scalar compensation.
 const ds=[];for(let n=0;n<81;n++){let x=n;const d=[];for(let i=0;i<4;i++){d.push(x%3-1);x=Math.floor(x/3)}ds.push(d);}
 for(const d of ds)for(let flags=0;flags<16;flags++){
   const mandate=!!(flags&1),review=!!(flags&2),path=!!(flags&4),baseline=!!(flags&8);
   const dominance=d.every(x=>x>=0)&&d.some(x=>x>0);
   const selection=mandate&&review&&path&&baseline&&dominance;
   const blockers=[!mandate,!review,!path,!baseline,d.some(x=>x<0),d.every(x=>x===0)];
   ck("selection",selection===!blockers.some(Boolean));
   if(selection)ck("scenario",Math.min(...d)>=0&&Math.max(...d)>0);
 }
 // Equal aggregate delta is not equal admissibility.
 for(const a of ds)for(const b of ds){
   const sum=x=>x.reduce((s,v)=>s+v,0);
   if(sum(a)===sum(b)&&a.every(x=>x>=0)&&b.some(x=>x<0))
      ck("baseline",a.every(x=>x>=0)!==b.every(x=>x>=0));
 }
 // Selection cannot prove execution or observation: exhaustive independent flags.
 for(let bits=0;bits<8;bits++){
   const selected=!!(bits&1),executed=!!(bits&2),observed=!!(bits&4);
   ck("realization", (selected&&executed&&observed)=== (bits===7));
 }
 return counts;
}
console.log(JSON.stringify(run()));
