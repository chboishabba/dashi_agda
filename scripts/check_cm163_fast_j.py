"""Euler pentagonal eta product and exact Newton inversion for J=q*j."""
from time import perf_counter
import argparse
import check_cm163_fast as fast
import check_cm163_modular_diagonal as base

def j_unit(n):
    assert n>=0
    e=[1]+[0]*n
    for d in range(1,n+1):
        a=240*d**3
        for k in range(d,n+1,d):e[k]+=a
    # Euler pentagonal theorem: P=prod(1-q^m).
    P=[1]+[0]*n
    k=1
    while k*(3*k-1)//2<=n:
        i,j=k*(3*k-1)//2,k*(3*k+1)//2
        P[i]=(-1)**k
        if j<=n:P[j]=(-1)**k
        k+=1
    P2=fast.mul(P,P,n);P4=fast.mul(P2,P2,n)
    P8=fast.mul(P4,P4,n);P16=fast.mul(P8,P8,n)
    delta=fast.mul(P8,P16,n)
    inv=[1]
    while len(inv)<=n:
        m=len(inv);k=min(2*m,n+1)
        v=fast.mul(delta[:k],inv,k-1)
        assert v[:m]==[1]+[0]*(m-1)
        inv+=fast.mul(inv,[-x for x in v[m:]],k-m-1)
    assert fast.mul(delta,inv,n)==[1]+[0]*n
    E3=fast.mul(fast.mul(e,e,n),e,n)
    J=fast.mul(E3,inv,n)
    assert fast.mul(delta,J,n)==E3
    return J

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--degree',type=int,default=3322);args=ap.parse_args()
    n=args.degree
    for k in (0,1,2,10,31,64):assert j_unit(k)==base.j_unit(k)
    fast.peak=fast.calls=0
    t=perf_counter();a=j_unit(n);tf=perf_counter()-t
    packed,calls=fast.peak,fast.calls
    t=perf_counter();b=base.j_unit(n);ts=perf_counter()-t
    assert a==b
    print('PASS',len(a),'coefficients, fast seconds',tf,'scalar seconds',ts,'packed bits',packed,'calls',calls,flush=True)

if __name__=='__main__':main()
