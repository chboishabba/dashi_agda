from check_pnp_boolean_separator import fold,replay,audit,Reservation
from itertools import product
from random import Random
from copy import deepcopy
from collections import Counter


def fib(n):
    a,b=0,1
    for _ in range(n):a,b=b,a+b
    return a


def main():
    rng=Random(3693501);C=Counter()
    for n in range(9):
        for _ in range(32):
            A=tuple(tuple(rng.randrange(-2,3) for j in range(n)) for i in range(rng.randrange(4)));b=tuple(rng.randrange(-2,3) for r in A)
            F=tuple(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for j in range(3)) for i in range(rng.randrange(4))) if n else ()
            H=tuple(tuple(rng.randrange(3) for j in range(n)) for i in range(rng.randrange(2)));t=tuple(rng.randrange(3) for r in H);O=tuple(tuple(j for j in range(n) if rng.randrange(2)) for i in range(rng.randrange(2)))
            W=[x for x in product((0,1),repeat=n) if audit(A,b,n,F,H,t,O,x,Reservation(10**7))]
            for clip in (None,2):
                q=fold(A,b,n,F,H,t,O,cap=10**7,clip=clip);assert q['status']==('WITNESS' if W else 'EMPTY');assert q['count']==(len(W) if clip is None else min(2,len(W)))
                if W:assert q['witness'] in W
                assert replay(A,b,n,F,H,t,O,q,10**7,clip=clip);C['mixed',q['status']]+=1
    # Nonlinear CNF of a path over affine-reopened pairs; total free d=k.
    for k in (16,32,64,128):
        n=2*k;A=tuple(tuple(int(j//2==i) for j in range(n)) for i in range(k));b=(1,)*k
        F=tuple((2*i+2,2*i+4) for i in range(k-1));q=fold(A,b,n,F,cap=10**8,max_width=2)
        assert q['count']==fib(k+2) and q['width']==2 and q['points']==4*k-2
        assert replay(A,b,n,F,(),(),(),q,10**8);print('affine_path',k,q['count'],q['points'],q['used'])
    # Centre shared by all leaves. Pinning one bit determines all leaves or frees them.
    for k in (16,32,64,128):
        F=tuple((1,i) for i in range(2,k+1));q=fold((),(),k,F,cap=10**8,max_width=2)
        assert q['count']==1+2**(k-1) and q['points']==4*k-2
        assert replay((),(),k,F,(),(),(),q,10**8)
        for b in (0,1):
            G=F+((1 if b else -1,),);z=fold((),(),k,G,cap=10**8,max_width=2,clip=2);assert z['count']==(2 if b else 1)
        print('star',k,q['count'],q['points'],q['used'])
    # Shared-boundary contradiction: both overlapping faces individually feasible.
    F=((1,2),(-1,-2),(2,3),(-2,-3),(1,3),(-1,-3))
    q=fold((),(),3,F,cap=10**6,max_width=3);assert q['status']=='EMPTY' and replay((),(),3,F,(),(),(),q,10**6)
    assert fold((),(),3,F,max_width=2)['status']=='UNKNOWN'
    F=((1,2),(2,3));q=fold((),(),3,F);z=deepcopy(q);z['trace'][0][3][(0,)]=100;assert not replay((),(),3,F,(),(),(),z,100000)
    z=deepcopy(q);z['trace'][0][3].pop((0,));assert not replay((),(),3,F,(),(),(),z,100000)
    assert not replay((),(),3,F,(),(),(),q,0)
    assert fold((),(),3,F,cap=0)['status']=='UNKNOWN'
    assert fold((),(),32,(tuple(range(1,33)),),max_width=12)['status']=='UNKNOWN'
    print(dict(C),'odd cycle, width refusal, tamper, omission, replay refusal PASS')
if __name__=='__main__':main()
