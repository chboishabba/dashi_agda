"""Source-derived signed weight ordering and safe interval pruning."""
from check_pnp_affine_accumulator import solve
from check_pnp_source_derived_cover import Reservation,Refused


def order(A,n,B):
    B.pay(1+n*(1+len(A)));weights=tuple(max((abs(r[j]) for r in A),default=0) for j in range(n))
    nonzero=[j for j in range(n) if weights[j]]
    if not nonzero:return tuple(range(n))
    pivot=min(nonzero,key=lambda j:(weights[j],j))
    # A heuristic, not an optimal pivot theorem. Large equal magnitude
    # positive/negative coefficients become adjacent after this pivot.
    B.pay(1+n*n)
    return (pivot,)+tuple(sorted((j for j in range(n) if j!=pivot),key=lambda j:(-weights[j],j)))


def run(A,b,n,F=(),H=(),t=(),O=(),cap=1000000,max_states=4096,clip=None):
    B=Reservation(cap)
    try:p=order(A,n,B)
    except Refused:return dict(status='UNKNOWN',used=cap-B.left)
    q=solve(A,b,n,F,H,t,O,B.left,clip,p,max_states,prune=True)
    return dict(q,used=cap-B.left+q['used'],permutation=p)


def main():
    from itertools import product
    from random import Random
    rng=Random(3693604);checks=0
    for n in range(9):
        for _ in range(32):
            A=tuple(tuple(rng.randrange(-8,9) for j in range(n)) for i in range(rng.randrange(3)));b=tuple(rng.randrange(-8,9) for i in A)
            F=tuple(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for j in range(3)) for i in range(rng.randrange(4))) if n else ()
            W=[x for x in product((0,1),repeat=n) if all(sum(v*y for v,y in zip(r,x))==s for r,s in zip(A,b)) and all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)]
            q=run(A,b,n,F,cap=10**7);assert q['count']==len(W)
            if W:assert q['witness'] in W
            checks+=1
    for k in (8,16,32,64):
        A=((1,)+tuple(4**i for i in range(1,k+1))+tuple(-4**i for i in range(1,k+1)),);n=2*k+1
        old=solve(A,(0,),n,cap=10**7,max_states=64,prune=True);assert old['status']=='UNKNOWN'
        q=run(A,(0,),n,cap=10**7,max_states=64);assert q['count']==2**k and q['peak']<=2
        print('paired_signed',k,n,old['status'],q['peak'],q['steps'],q['used'])
    assert run(((1,),),(0,),1,cap=0)['status']=='UNKNOWN'
    print('pruned independent',checks,'refusal PASS')
if __name__=='__main__':main()
