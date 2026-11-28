"""Original incidence modular refutation; prime powers, not field conflation."""
from itertools import combinations,product
from check_pnp_source_derived_cover import Reservation,Refused
from check_pnp_frontier_resolution import norm
from check_pnp_hall_geometry import flow


def contradiction(A,b,n,p,e,B):
    # Only fixed small primes are admitted by this producer.
    if p not in (2,3,5,7) or not 1<=e<=16 or len(A)!=len(b) or any(len(r)!=n for r in A):raise ValueError('shape')
    m=p**e;r=len(A);B.pay(1+r*(n+r+1))
    D=[[v%m for v in a]+[t%m]+[int(i==j) for j in range(r)] for i,(a,t) in enumerate(zip(A,b))]
    q=m;active=list(range(n));steps=0
    while D:
        B.pay(1+len(D)*(len(active)+1))
        pivot=next(((i,j) for i,row in enumerate(D) for j in active if row[j]%p),None)
        if pivot is not None:
            i,j=pivot;B.pay(1+len(D)*(n+r+1));row=D.pop(i);u=pow(row[j],-1,q)
            row=[v*u%q for v in row[:n+1]]+[v*u%m for v in row[n+1:]]
            for k,z in enumerate(D):
                v=z[j];D[k]=[(a-v*c)%q for a,c in zip(z[:n+1],row[:n+1])]+[(a-v*c)%m for a,c in zip(z[n+1:],row[n+1:])]
            active.remove(j);steps+=1;continue
        for row in D:
            if row[n]%p:
                y=tuple((q//p)*v%m for v in row[n+1:]);B.pay(1+r*(n+1))
                assert verify(A,b,n,m,y)
                return dict(modulus=m,weights=y,steps=steps,divisions=e-next(k for k in range(1,e+1) if p**k==q))
        if q==p:return None
        B.pay(1+len(D)*(n+1));q//=p
        D=[[v//p for v in row[:n+1]]+row[n+1:] for row in D]
    return None


def verify(A,b,n,m,y):
    return (m>=2 and len(A)==len(b)==len(y) and all(len(row)==n for row in A)
        and all(0<=v<m for v in y) and all(sum(c*a[j] for c,a in zip(y,A))%m==0 for j in range(n))
        and sum(c*t for c,t in zip(y,b))%m!=0)


def incidence(O,n):
    if any(len(set(c))!=len(c) or any(not 0<=v<n for v in c) for c in O):raise ValueError('incidence')
    return tuple(tuple(int(i in s) for i in range(n)) for s in map(set,O)),(1,)*len(O)


def exact_rows(F,n,B):
    # Positive clause + ALL pairwise exclusions, checked on original CNF.
    if n<0 or any(not 1<=abs(l)<=n for c in F for l in c):raise ValueError('source')
    B.pay(1+n+sum(1+len(c) for c in F));D=set(map(norm,F));O=[]
    for c in sorted(D):
        if not c or min(c)<0:continue
        B.pay(1+len(c)**2)
        if all(norm((-a,-b)) in D for a,b in combinations(c,2)):O.append(tuple(v-1 for v in c))
    return tuple(O)


def solve(F,n,O,cap,moduli=((2,1),(3,1),(2,2),(2,3),(2,4),(2,5))):
    B=Reservation(cap);tested=[]
    try:
        if O is None:O=exact_rows(F,n,B)
        B.pay(1+(n+1)*len(O));A,b=incidence(O,n)
        for p,e in moduli:
            z=contradiction(A,b,n,p,e,B);tested.append(p**e)
            if z is not None:return dict(status='EMPTY',rows=O,certificate=z,tested=tuple(tested),used=cap-B.left)
        return dict(status='RESIDUAL',rows=O,tested=tuple(tested),used=cap-B.left)
    except Refused:return dict(status='UNKNOWN',tested=tuple(tested),used=cap-B.left)


def latin(k):
    T=tuple((a,b,(a+b)%k) for a,b in product(range(k),repeat=2))
    O=tuple(tuple(j for j,t in enumerate(T) if t[d]==i) for d in range(3) for i in range(k))
    return T,O


def main():
    from random import Random
    rng=Random(3693301);checks=certs=0
    for p,e in ((2,1),(2,2),(2,3),(3,1),(3,2),(5,1)):
        m=p**e
        for n in range(4):
            for _ in range(48):
                r=rng.randrange(5);A=tuple(tuple(rng.randrange(m) for i in range(n)) for j in range(r));b=tuple(rng.randrange(m) for j in range(r))
                feasible=any(all(sum(a*v for a,v in zip(row,x))%m==t for row,t in zip(A,b)) for x in product(range(m),repeat=n))
                z=contradiction(A,b,n,p,e,Reservation(10**7));assert (z is None)==feasible
                if z is not None:assert verify(A,b,n,m,z['weights']);certs+=1
                checks+=1
    print('linear',checks,'certificates',certs)
    for k in (2,4,8,16,32):
        T,O=latin(k);n=len(T);L=tuple(range(k));E=set(product(L,repeat=2))
        for a,b in combinations(range(3),2):assert {(t[a],t[b]) for t in T}==E
        assert flow(L,L,E,Reservation(10**7)) is None
        z=solve((),n,O,10**8);assert z['status']=='EMPTY' and z['certificate']['modulus']==k
        A,b=incidence(O,n);assert verify(A,b,n,k,z['certificate']['weights'])
        print('latin',k,n,z['tested'],z['used'])
    for k in (1,3,5,7):
        T,O=latin(k);z=solve((),len(T),O,10**8);assert z['status']=='RESIDUAL'
        x=tuple(int(a==b) for a,b,c in T);assert all(sum(x[i] for i in row)==1 for row in O)
    T,O=latin(4);F=tuple(tuple(v+1 for v in c) for c in O)+tuple((-a-1,-b-1) for c in O for a,b in combinations(c,2))
    z=solve(F,len(T),None,10**7);assert z['status']=='EMPTY' and z['certificate']['modulus']==4
    G=((1,2),(1,3),(2,3),(-1,-3),(-2,-3))
    q=solve(G,3,None,10**7);assert q['status']=='RESIDUAL' and (0,1) not in q['rows']
    assert solve(F,len(T),None,0)['status']=='UNKNOWN'
    A,b=incidence(O,len(T));assert not verify(A,b,len(T),4,(0,)*len(O))
    print('source extraction, missing exclusion, tamper, refusal PASS')
if __name__=='__main__':main()
