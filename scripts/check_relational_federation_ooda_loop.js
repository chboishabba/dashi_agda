// Synthetic finite controls, not real observations, proof kernel or authorisation.
function run(){
 const counts={refinement:0,closure:0,contradiction:0,moveAuthority:0,identity:0,revision:0};
 const ck=(k,b)=>{if(!b)throw Error(k);counts[k]++};
 const members=m=>[0,1,2,3].filter(i=>m&(1<<i));
 const constant=(m,c)=>{const h=members(m);return h.length>0&&h.every(i=>((c>>i)&1)===((c>>h[0])&1));};
 // Every live subset, every observational support, every binary consumer.
 for(let prior=0;prior<16;prior++)for(let support=0;support<16;support++){
   const post=prior&support;
   ck("refinement",members(post).every(h=>members(prior).includes(h)&&members(support).includes(h)));
   for(let c=0;c<16;c++){
     if(post===0)ck("contradiction",!constant(post,c));
     if(post!==0&&constant(prior,c))ck("closure",constant(post,c));
   }
 }
 // think/look/test/act, respective authority and exact binding.
 for(let kind=0;kind<4;kind++)for(let mask=0;mask<16;mask++){
   const authority=!!(mask&1),binding=!!(mask&2),admitted=!!(mask&4),review=!!(mask&8);
   const canAct=kind===3&&authority&&binding&&admitted&&review;
   ck("moveAuthority",canAct===(kind===3&&mask===15));
 }
 // Same candidate ID must occur on the same source revision.
 for(let source=0;source<3;source++)for(let candidate=0;candidate<3;candidate++)
 for(let receiptSource=0;receiptSource<3;receiptSource++)for(let receiptCandidate=0;receiptCandidate<3;receiptCandidate++){
   const exact=source===receiptSource&&candidate===receiptCandidate;
   ck("identity",exact===([source,candidate].join(":")===[receiptSource,receiptCandidate].join(":")));
 }
 // A model revision cannot rewrite the pre-revision evidence; a changed
 // model can change which consumer is constant on the same live fibre.
 for(let live=1;live<16;live++)for(let old=0;old<16;old++)for(let next=0;next<16;next++){
   const oldReceipt=Object.freeze({live,model:old,closed:constant(live,old)});
   const newReceipt={live,model:next,closed:constant(live,next)};
   ck("revision",oldReceipt.model===old&&oldReceipt.closed===constant(live,old)&&newReceipt.closed===constant(live,next));
 }
 return counts;
}
console.log(JSON.stringify(run()));
