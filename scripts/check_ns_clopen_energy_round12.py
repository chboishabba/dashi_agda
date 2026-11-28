"""Exact prefix geometry and Fourier tail controls, not Lean or PDE acceptance."""
from fractions import Fraction as Q
from itertools import product
from random import Random
import sympy as S
if not __debug__:raise SystemExit('refusing optimized execution')

def prefix():
    rng=Random(36912);count=0
    for dim in (1,2,3,6,12):
        for _ in range(24):
            x=tuple(Q(rng.randrange(-18,19),36*dim) for _ in range(dim))
            E=sum(z*z for z in x)
            lo=[Q(-1)]*dim;hi=[Q(1)]*dim
            for n in range(1,13):
                w=Q(2,3**n)
                for i,z in enumerate(x):
                    children=[(lo[i]+j*w,lo[i]+(j+1)*w) for j in range(3)]
                    assert children[0][0]==lo[i] and children[-1][1]==hi[i]
                    assert children[0][1]==children[1][0] and children[1][1]==children[2][0];count+=2
                    j=next(j for j,(a,b) in enumerate(children) if a<=z<=b)
                    a,b=children[j];assert lo[i]<=a<=z<=b<=hi[i];count+=1
                    lo[i],hi[i]=a,b
                nearest=[a if a>0 else b if b<0 else Q(0) for a,b in zip(lo,hi)]
                assert sum(z*z for z in nearest)<=E;count+=1
                assert all(b-a==w for a,b in zip(lo,hi));count+=1
    # Shared endpoints prevent a disjoint ambient real clopen partition.
    assert Q(1,3) in (Q(0),Q(1,3)) and Q(1,3) in (Q(1,3),Q(2,3));count+=1
    return count

def tails():
    rng=Random(369);count=0
    for N in range(1,6):
        K=[k for k in product(range(-N,N+1),repeat=3) if any(k)]
        masses={k:sum(z*z for z in k) for k in K}
        for _ in range(4):
            w={k:Q(rng.randrange(0,9),17) for k in K}
            D=sum(masses[k]*w[k] for k in K)
            for R in range(1,N+3):
                H=[k for k in K if R*R<=masses[k]]
                assert R*R*sum(w[k] for k in H)<=D;count+=1
                # exact pointwise half-order bound: R sqrt(m)<=m iff R²<=m.
                assert all(R*R*masses[k]<=masses[k]**2 for k in H);count+=1
    # Exact real heat shear solutions: t=log(2), nu=1, a_n(t)=a_n(0) exp(-n² t).
    # Each coefficient and its conjugate at -n have equal squared amplitude.
    for N in range(1,13):
        A={n:Q(rng.randrange(0,6),7) for n in range(1,N+1)}
        E0=sum(2*a*a for a in A.values());ET=sum(2*a*a*Q(1,2**(2*n*n)) for n,a in A.items())
        ID=sum(a*a*(1-Q(1,2**(2*n*n))) for n,a in A.items())
        assert ET+2*ID==E0;count+=1
        for R in range(1,N+2):
            IE=sum(a*a*(1-Q(1,2**(2*n*n)))/n**2 for n,a in A.items() if n>=R)
            IH=sum(a*a*(1-Q(1,2**(2*n*n)))/n for n,a in A.items() if n>=R)
            assert IE<=E0/(2*R**2);count+=1
            assert IH<=E0/(2*R);count+=1
    # Energy ball bounded but not strongly precompact across cutoffs:
    # normalized transverse shear on distinct Fourier modes (positive and negative).
    for n in range(1,65):
        U={n:Q(1),-n:Q(1)}
        assert sum(a*a for a in U.values())==2;count+=1
        assert sum(abs(k)*a*a for k,a in U.items())==2*n;count+=1
        for m in range(1,n):
            V={m:Q(1),-m:Q(1)}
            assert sum((U.get(k,0)-V.get(k,0))**2 for k in U.keys()|V.keys())==4;count+=1
    return count

def scalar_flow():
    t,nu,k,a=S.symbols('t nu k a',real=True)
    u=a*S.exp(-nu*k*k*t)
    assert S.simplify(S.diff(u,t)+nu*k*k*u)==0
    assert S.simplify(S.diff(2*u*u,t)+2*nu*k*k*(2*u*u))==0
    # Exact overlap of two time charts, same physical scalar heat mode.
    s=S.symbols('s',real=True)
    assert S.simplify(u.subs(t,s)*S.exp(-nu*k*k*(t-s))-u)==0
    return 3

if __name__=='__main__':
    p,q,r=prefix(),tails(),scalar_flow()
    print('SymPy',S.__version__,'prefix',p,'tail',q,'scalar-flow',r,'TOTAL',p+q+r,'PASS')
