"""One declared allowance and one separately metered bit-data schedule."""
from random import Random
from collections import Counter
from check_pnp_bit_data_schedule import Clock
from check_pnp_integrated_source_campaign import check
from check_pnp_typed_portfolio import ContinuationAllowance,cnf_dispatch,hard_dispatch

def main():
    rng=Random(36943);C=Counter();data=Clock(10**8)
    for n in range(9):
        for k in range(16):
            F=tuple(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(min(n,4)+1))) for _ in range(k%7))
            rows=(tuple(rng.randrange(3) for i in range(n)),)
            for t in range(3):
                for cap in (0,4096,10**7):
                    q=check(F,n,rows,(t,),cap,data_clock=data)
                    C[cap,q['status']]+=1
    assert C[4096,'WITNESS']==157 and C[4096,'EMPTY']==249 and C[4096,'UNKNOWN']==26
    assert C[10**7,'WITNESS']==183 and C[10**7,'EMPTY']==249
    root=ContinuationAllowance(10**7)
    assert cnf_dispatch(((1,),),1,(),(),root,10**6,data_clock=data)['status']=='WITNESS'
    q=hard_dispatch(2,(3,),(),(0,),3,(),root,3*10**6,data_clock=data)
    assert q['status']=='IMPROVED' and q['potential']==0
    q=cnf_dispatch(((1,),),1,(),(),root,10**6,data_clock=Clock(0))
    assert q['status']=='WITNESS_DATA_AUDIT_REFUSED' and q['witness']==(1,)
    assert sum(root.charges.values())+root.left==root.total
    assert sum(data.count.values())+data.left==data.cap
    print(dict(C),dict(data.count),data.cap-data.left)
if __name__=='__main__':main()
