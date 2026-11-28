"""Actual shared logical allowance; original hard endpoints and traces."""
from itertools import product
from collections import Counter
from check_pnp_typed_portfolio import ContinuationAllowance,cnf_dispatch,hard_dispatch,satisfies

def main():
    root=ContinuationAllowance(100_000_000);C=Counter()
    q=cnf_dispatch(((1,2),),2,((1,2),),(0,),root,1_000_000)
    assert q['status']=='WITNESS' and q['witness']==(1,1)
    C['cnf']+=1
    for H,flats,x in product(((),((3,0),),((3,1),)),((),(((1,0),(2,0)),)),range(4)):
        if not satisfies(x,H,flats):continue
        R=(3,);caps=(0,);phi=lambda y:y.bit_count()
        best=min(phi(y) for y in range(4) if satisfies(y,H,flats))
        q=hard_dispatch(2,R,H,caps,x,flats,root,3_000_000)
        status=q['status'];C[status]+=1
        if status=='SAT':assert phi(x)==0
        elif status=='MINIMUM':assert phi(x)==best
        elif status in ('IMPROVED','IMPROVED_ENDPOINT_NO_TRACE'):
            y=q['witness'];assert satisfies(y,H,flats) and phi(y)<phi(x)
            if status=='IMPROVED':
                t=q['trace'];assert t['start']==x and t['end']==y and t['decrease']==phi(x)-phi(y)
                assert all(satisfies(m['after'],H,flats) for m in t['macros'])
        else:raise AssertionError(q)
    assert sum(root.charges.values())+root.left==root.total
    before=root.left
    assert hard_dispatch(2,(3,),(),(0,),3,(),root,before+1)['status']=='UNKNOWN'
    assert root.left==before
    C['refusal']=1
    print(dict(C),dict(root.charges))
if __name__=='__main__':main()
