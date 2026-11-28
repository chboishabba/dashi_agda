"""Independent exact regression for original finite carriers and phase core.
Phase source argument may be full repo file or exact extracted core. This
checks the actual core functions with independent RREF/character arithmetic;
not production CNF integration, native Lean, or an infinite PDE proof.
"""
from itertools import product, combinations_with_replacement
from pathlib import Path
from random import Random
from fractions import Fraction as Q
import argparse, json, math, hashlib
import sympy as s


def span(rows,n):
    A=[list(a) for a in rows];k=0
    for j in range(n):
        i=next((i for i in range(k,len(A)) if A[i][j]),None)
        if i is None:continue
        A[k],A[i]=A[i],A[k];A[k]=[x*A[k][j]%3 for x in A[k]]
        for i in range(len(A)):
            if i!=k:A[i]=[(x-A[i][j]*y)%3 for x,y in zip(A[i],A[k])]
        k+=1
    return tuple(tuple(row) for row in A[:k])

Z=(0,0);ONE=(1,0);OMEGA=(ONE,(0,1),(-1,-1))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]-a[1]*b[1])
def phase(a,d):return mul(a,OMEGA[d%3])


def load_core(path):
    raw=path.read_text();core=raw[raw.index('class Refusal'):raw.index('\ndef singleton')] if '\ndef singleton' in raw else raw
    env=dict(product=product,combinations_with_replacement=combinations_with_replacement,
             Z=Z,ONE=ONE,OMEGA=OMEGA,add=add,mul=mul,phase=phase,span=span)
    exec(compile(core,str(path),'exec'),env)
    print('phase core bytes',len(core.encode()),'sha256',hashlib.sha256(core.encode()).hexdigest())
    return env


def phase_checks(env):
    rng=Random(36920261128);out=dict(interpolate=0,recognize=0,pullback=0,contraction=0,refusal=0)
    p=env['cubic_interpolation'];pull=env['pull_cubic'];g=env['conditional_gauss'];rec=env['recognize'];linear=env['linear'];ev=env['evaluate'];noop=lambda _:None
    def ref(P,x):return sum(a*math.prod(x[i] for i in m) for m,a in P.items())%3
    for n in range(1,6):
        mons=[m for k in range(4) for m in combinations_with_replacement(range(n),k) if all(m.count(i)<=2 for i in set(m))]
        X=list(product(range(3),repeat=n))
        for j in range(40):
            P={m:a for m in mons if (a:=rng.randrange(3))};D={x:ref(P,x) for x in X}
            assert p(D,n,noop)==P;out['interpolate']+=1
            T={x:OMEGA[e] for x,e in D.items()};a,u,V,R=rec(T,n,noop,3)
            assert all(phase(a,ref(R,x))==T[x] for x in X);out['recognize']+=1
            A=[[rng.randrange(3) for _ in range(n)] for _ in range(n)];b=[rng.randrange(3) for _ in range(n)]
            R=pull(P,[linear(c,v) for c,v in zip(b,A)],noop)
            for x in X:
                y=tuple((c+sum(v*z for v,z in zip(row,x)))%3 for c,row in zip(b,A))
                assert ev(R,x)==ref(P,y);out['pullback']+=1
            hist=[sum(e==a for e in D.values()) for a in range(3)]
            assert g(P,n,noop,[3**n])==(hist[0]-hist[2],hist[1]-hist[2]);out['contraction']+=1
    P={(0,1,2):1};X=list(product(range(3),repeat=3));T={x:OMEGA[ref(P,x)] for x in X}
    assert rec(T,3,noop,2) is None;out['refusal']+=1
    assert rec({(0,):ONE,(1,):ONE},1,noop,3) is None;out['refusal']+=1
    try:g(P,3,noop,[1])
    except env['Refusal']:out['refusal']+=1
    else:raise AssertionError('phase branch cap not enforced')
    return out


def ns_checks():
    # Exact Gaussian rationals represented as Python complex pairs of Fractions.
    def plus(a,b):return a[0]+b[0],a[1]+b[1]
    def times(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
    def scale(a,c):return a[0]*c,a[1]*c
    def conj(a):return a[0],-a[1]
    def neg(a):return -a[0],-a[1]
    z=(Q(0),Q(0));I=(Q(0),Q(1));zero=(0,0,0)
    K=list(product(range(-1,2),repeat=3));U={};rng=Random(369)
    def dot(k,u):
        t=z
        for a,b in zip(k,u):t=plus(t,scale(b,a))
        return t
    def project(k,u):
        n=sum(a*a for a in k)
        return tuple(plus(v,scale(dot(k,u),-Q(a,n))) for a,v in zip(k,u)) if n else tuple(u)
    for k in K:
        if k==zero:U[k]=(z,)*3
        elif k not in U:
            u=project(k,tuple((Q(rng.randrange(-2,3)),Q(rng.randrange(-2,3))) for _ in k))
            U[k]=u;U[tuple(-a for a in k)]=tuple(conj(v) for v in u)
    N={};counts=dict(ordered=0,transverse=0,reality=0,rate=0)
    for k in K:
        if k==zero:continue
        f=[z]*3
        for p,q in product(K,repeat=2):
            if tuple(a+b for a,b in zip(p,q))!=k:continue
            v=project(k,tuple(times(dot(q,U[p]),x) for x in U[q]))
            rhs=tuple(times(neg(I),x) for x in v)
            div=project(k,tuple(times(I,times(dot(k,U[p]),x)) for x in U[q]))
            assert rhs==tuple(neg(x) for x in div);counts['ordered']+=1
            assert sum(a*a+b*b for a,b in zip(p,q))>0;counts['rate']+=1
            f=list(map(plus,f,rhs))
        assert dot(k,f)==z;counts['transverse']+=1
        N[k]=tuple(f)
    for k,u in N.items():
        assert N[tuple(-a for a in k)]==tuple(conj(x) for x in u);counts['reality']+=1
    return counts


def hodge_checks():
    # Independent exact signed fibre checks, nonzero discriminants and
    # both signs of the prescribed product. Not a cycle-class test.
    rng=Random(3697);count=0
    for _ in range(64):
        d=tuple(Q(rng.choice((-1,1))*rng.randrange(1,12),rng.randrange(1,8)) for i in range(6));base=math.prod(d)
        for eps in (-1,1):
            delta=eps*base;D=tuple(x*x for x in d)
            assert delta*delta==math.prod(D)
            lifts=[tuple(e*x for e,x in zip(signs,d)) for signs in product((-1,1),repeat=6) if math.prod(signs)==eps]
            assert len(set(lifts))==32
            for u in lifts:
                assert math.prod(u)==delta and tuple(x*x for x in u)==D
                ratio=tuple(a/b for a,b in zip(u,lifts[0]));assert math.prod(ratio)==1 and all(x*x==1 for x in ratio)
                count+=1
    a,y,z=s.symbols('a y z',nonzero=True);B=-3*a*a+3*a+1
    Q0=-3*a**3-3*a*a*z-a*a+3*a*z+3*a-2*z*z+z+3
    Delta=B*B+8*(-3*a**3-a*a+3*a+3-y-a**7/y)
    assert s.cancel((B-4*z)**2-Delta+8*(Q0-y-a**7/y))==0
    return dict(deck_lifts=count,chart_identity=1)


if __name__=='__main__':
    if not __debug__:raise SystemExit('refusing optimized execution')
    p=argparse.ArgumentParser();p.add_argument('--phase-source',type=Path,required=True);a=p.parse_args()
    counts={**phase_checks(load_core(a.phase_source)),**ns_checks(),**hodge_checks()}
    print(json.dumps(counts,sort_keys=True),'TOTAL',sum(counts.values()),'PASS')
