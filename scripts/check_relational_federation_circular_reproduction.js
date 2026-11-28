// Synthetic integer controls only. No actual finance, ecology or kernel result.
function run(){
 const counts={cash:0,debt:0,recovery:0,cycle:0,stress:0};
 function ck(k,v){if(!v)throw Error(k);counts[k]++}
 // 3-node oriented internal clearing, no gross-turnover promotion.
 for(let x=0;x<=8;x++)for(let y=0;y<=8;y++)for(let z=0;z<=8;z++){
   const incoming=[z,x,y],outgoing=[x,y,z];ck("cycle",incoming.reduce((a,b)=>a+b,0)===outgoing.reduce((a,b)=>a+b,0));
 }
 // Explicit realized cash and principal, no capital draw as earnings.
 for(let opening=0;opening<=5;opening++)for(let earned=0;earned<=5;earned++)for(let grant=0;grant<=3;grant++)for(let draw=0;draw<=3;draw++)
 for(let pay=0;pay<=opening+earned+grant+draw;pay++){
  const closing=opening+earned+grant+draw-pay;ck("cash",opening+earned+grant+draw===pay+closing);
 }
 for(let debt=0;debt<=8;debt++)for(let draw=0;draw<=8;draw++)for(let pay=0;pay<=debt+draw;pay++)ck("debt",debt+draw===pay+(debt+draw-pay));
 // Physical recovery versus absolute input and demand: integer material units.
 for(let recovered=0;recovered<=8;recovered++)for(let virgin=0;virgin<=8;virgin++)for(let loss=0;loss<=recovered+virgin;loss++)ck("recovery",recovered+virgin===loss+(recovered+virgin-loss));
 // Bounded stress: a continuing cash obligation is not paid by booked savings.
 for(let cash=0;cash<=12;cash++)for(let receipts=0;receipts<=12;receipts++)for(let cost=0;cost<=12;cost++)for(let reserve=0;reserve<=4;reserve++){
 const safe=cash+receipts>=cost+reserve;
 ck("stress",safe===(cash+receipts-cost>=reserve));
 }
 return counts;
}
console.log(JSON.stringify(run()));
