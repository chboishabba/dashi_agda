"""Exact rational one-free-coordinate cut on original integer incidence."""
from fractions import Fraction as Q
from itertools import product,combinations,permutations
from check_pnp_prime_power_incidence import incidence,solve as modular
from check_pnp_source_derived_cover import Reservation,Refused
from check_pnp_hall_geometry import flow


def solve(O,n,cap):
    B=Reservation(cap);r=len(O)
    try:
        B.pay(1+r*(n+r+1));A,b=incidence(O,n)
        D=[[Q(v) for v in a]+[Q(t)]+[Q(i==j) for j in range(r)] for i,(a,t) in enumerate(zip(A,b))];P=[]
        for j in range(n):
            B.pay(1+r);k=next((i for i in range(len(P),r) if D[i][j]),None)
            if k is None:continue
            i=len(P);P.append(j);D[i],D[k]=D[k],D[i];B.pay(1+r*(n+r+1));u=D[i][j];D[i]=[a/u for a in D[i]]
            for k in range(r):
                if k==i:continue
                u=D[k][j];D[k]=[a-u*c for a,c in zip(D[k],D[i])]
        B.pay(1+r*r*(n+1))
        for row in D:
            assert all(sum(c*a[j] for c,a in zip(row[n+1:],A))==row[j] for j in range(n))
            assert sum(c*t for c,t in zip(row[n+1:],b))==row[n]
            if not any(row[:n]) and row[n]:return dict(status='EMPTY',receipt=tuple(map(tuple,D)),used=cap-B.left)
        free=tuple(j for j in range(n) if j not in P)
        if len(free)>1:return dict(status='UNKNOWN',free=len(free),used=cap-B.left)
        # Every Boolean solution has these 0/1 free coordinates, and
        # every remaining coordinate is uniquely forced by its row.
        for bits in product((0,1),repeat=len(free)):
            B.pay(1+n+r*(n+1));x=[Q(0)]*n
            for j,v in zip(free,bits):x[j]=Q(v)
            for i,j in enumerate(P):x[j]=D[i][n]-sum(D[i][k]*x[k] for k in free)
            if all(v in (0,1) for v in x):
                assert all(sum(x[j] for j in c)==1 for c in O)
                return dict(status='WITNESS',witness=tuple(map(int,x)),used=cap-B.left)
        return dict(status='EMPTY',receipt=tuple(map(tuple,D)),free=free,used=cap-B.left)
    except Refused:return dict(status='UNKNOWN',used=cap-B.left)


def main():
    from random import Random
    T=((0,0,2),(0,1,0),(0,2,2),(1,0,2),(1,2,0),(1,2,1),(2,0,1),(2,1,2));n=len(T);L=tuple(range(3))
    O=tuple(tuple(j for j,t in enumerate(T) if t[d]==i) for d in range(3) for i in L)
    A,b=incidence(O,n);z=(-1,1,1,1,0,0,1,0);f=(Q(1,5),Q(3,5),Q(1,5),Q(1,5),Q(2,5),Q(2,5),Q(3,5),Q(2,5))
    for x in (z,f):assert all(sum(x[j] for j in c)==1 for c in O)
    assert all(0<=v<=1 for v in f)
    edges=0
    for a,b in combinations(range(3),2):
        E={(t[a],t[b]) for t in T}
        for u,v in E:
            assert flow(tuple(i for i in L if i!=u),tuple(j for j in L if j!=v),E,Reservation(10**6)) is None;edges+=1
    assert not any(all((a,p[a],q[a]) in T for a in L) for p in permutations(L) for q in permutations(L))
    assert modular((),n,O,10**7)['status']=='RESIDUAL'
    q=solve(O,n,10**7);assert q['status']=='EMPTY' and len(q['free'])==1
    print('joint counterexample',n,'pair supports',edges,'free',q['free'],'logical used',q['used'])
    rng=Random(3693304);checks=complete=0
    for n in range(1,9):
        for _ in range(32):
            O=tuple(tuple(i for i in range(n) if rng.randrange(2)) for j in range(rng.randrange(n+3)))
            W=[x for x in product((0,1),repeat=n) if all(sum(x[i] for i in c)==1 for c in O)]
            q=solve(O,n,10**7);checks+=1
            if q['status']!='UNKNOWN':
                assert q['status']==('WITNESS' if W else 'EMPTY');complete+=1
                if W:assert q['witness'] in W
    assert solve(((0,),),1,0)['status']=='UNKNOWN'
    print('random',checks,'completed',complete)
if __name__=='__main__':main()
