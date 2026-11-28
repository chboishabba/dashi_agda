"""Native original-event birth/extinction acceptance on real padded species coordinates."""
import numpy as np
from solar_support_transition import support_transition
from solar_physical_causal import event


def fixtures():
    volume=5.
    cases=(
        (np.array([0.,0.,0.]),np.array([0.,0.,0.]),np.array([3.,2.,1.])),
        (np.array([3.,2.,1.]),np.array([3.,2.,1.]),np.array([0.,0.,0.])),
        (np.array([3.,2.,1.]),np.array([1.,1.,0.]),np.array([1.,1.,0.])))
    receipts=[]
    for index,(n,r,c) in enumerate(cases):
        z=np.zeros((3,3)) if index==0 else np.arange(9,dtype=float).reshape(3,3)*1e-12
        birth=np.ones((3,3))*.2
        a,new,ledger,receipt=support_transition(z,n,r,c,birth,volume)
        direct=event(z,n,r,c,birth,volume)
        assert np.array_equal(a,direct[0])
        assert np.array_equal(new,direct[1])
        assert np.array_equal(ledger,direct[2])
        assert receipt['support_changed']==(index!=2)
        assert receipt['full_generator_jvp_admitted']==(index==2)
        receipts.append(receipt)
    rejected=False
    try:
        support_transition(np.ones(9),np.zeros(3),np.zeros(3),
                           np.zeros(3),np.zeros((3,3)),1.)
    except ValueError:rejected=True
    assert rejected
    return dict(status='PASS',cases=len(receipts),
                births=len(receipts[0]['born_species']),
                extinctions=len(receipts[1]['extinct_species']),
                unchanged_support=True,negative_control=True)
if __name__=='__main__':
    print(fixtures())
