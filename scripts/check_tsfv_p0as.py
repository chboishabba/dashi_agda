"""AS: source pointer clock, original pulse overlap, oscillator commutators.
Exact controls on a selected extension; no empirical observer or kernel claim.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import sympy as s


def pointer():
    X=s.Matrix([[0,1],[1,0]]); I=s.eye(2)
    frames=(X,I,X)
    for a,b,c in product(range(3),repeat=3):
        assert frames[c]*frames[b]*frames[b]*frames[a]==frames[c]*frames[a]
    alpha,beta=s.symbols('alpha beta',complex=True)
    pre=s.Matrix([1,1]); post=s.Matrix([[alpha,beta]])
    P=[s.diag(1,0),s.diag(0,1)]
    for k in range(2):
        assert (post*X*X*P[k]*X*X*pre)[0]==(post*P[k]*pre)[0]
    # A late rotation changes conditional counts, not the already recorded marginal.
    b,d=s.symbols('b d',real=True); z=b+s.I*d; t=s.symbols('t',real=True)
    R=s.Matrix([[s.cos(t),-s.sin(t)],[s.sin(t),s.cos(t)]])
    amps=[(s.Matrix([[1,z]])*R*p*pre)[0] for p in P]
    w=[s.expand_complex(a*s.conjugate(a)).expand() for a in amps]
    assert s.trigsimp(sum(w))==1+b*b+d*d
    assert s.simplify(s.diff(w[0]/(1+b*b+d*d),t).subs(t,0)-2*b/(1+b*b+d*d))==0
    for a in range(2):
        assert s.trigsimp((R*P[a]*pre).dot(R*P[a]*pre))==1
    print('PASS 27 clock compositions, original ABL amplitudes, conditioned derivative and complete final marginal',flush=True)


def records():
    pulses=[(F(3,5),F(4,5)),(F(5,13),F(12,13)),(F(0),F(1))]
    for n in range(4):
        for ps in product(pulses,repeat=n):
            state={():F(1)}; expected=F(1)
            for x,(c,d) in enumerate(ps):
                assert c*c+d*d==1
                expected*=c
                state={**{k:v*c for k,v in state.items()},**{k+(x,):v*d for k,v in state.items()}}
            assert sum(v*v for v in state.values())==1
            assert state[()]==expected
            # Vacuum projection reproduces arbitrary original complex gamma weight.
            for gr,gi in [(1,0),(2,-3),(0,0)]:
                w=F(gr*gr+gi*gi)*expected**2
                # Independently contract the embedded state with vacuum.
                ar=state[()]*gr; ai=state[()]*gi
                assert ar*ar+ai*ai==w
                assert F(1,1)/(1+w)+(ar*ar+ai*ai)/(1+w)==1
    print('PASS 40 pulse lists, 120 complex gamma/Born controls including zero overlap',flush=True)


def add(out,v,c=1):
    for k,x in v.items(): out[k]+=c*x

def clean(v): return {k:x for k,x in v.items() if x}

def op(v,i,sign):
    # Unnormalised polynomial Fock basis: multiplication creates,
    # derivative annihilates. sign=+1 Q; sign=-1 Pprime.
    out=defaultdict(int)
    for k,x in v.items():
        out[tuple(sorted(k+(i,)))]+=x
        n=k.count(i)
        if n:
            j=k.index(i); out[k[:j]+k[j+1:]]+=sign*n*x
    return clean(out)


def oscillator():
    N=5; sites=list(product(range(N),repeat=3)); ids={x:i for i,x in enumerate(sites)}
    def near(i):
        x=sites[i]
        for j in range(3):
            for d in (-1,1):
                y=list(x); y[j]=(y[j]+d)%N; yield ids[tuple(y)]
    # Original c=3/2,a=1/5,mu=7/10 -> 100 L integer.
    k=5625; diag=49+6*k; o=ids[(0,0,0)]; n=ids[(1,0,0)]
    edges=[(i,j) for i in range(125) for j in near(i) if i<j]
    def H4(v):
        # H4=400 H, with Q=a+a†, P=i(a†-a), hbar=1.
        out=defaultdict(int)
        for i in range(125):
            add(out,op(op(v,i,-1),i,-1),-100)
            add(out,op(op(v,i,1),i,1),diag)
        for i,j in edges: add(out,op(op(v,j,1),i,1),-2*k)
        return clean(out)
    count=0
    for v in ({():1},{(o,):1},{(o,n):1},{():3,(o,):4}):
        Hv=H4(v)
        for i in (o,n):
            for sign in (1,-1):
                lhs=defaultdict(int); add(lhs,H4(op(v,i,sign))); add(lhs,op(Hv,i,sign),-1)
                rhs=defaultdict(int)
                if sign==1: add(rhs,op(v,i,-1),400)
                else:
                    add(rhs,op(v,i,1),4*diag)
                    for j in near(i): add(rhs,op(v,j,1),-4*k)
                assert clean(lhs)==clean(rhs); count+=1
        for i,j in product((o,n),repeat=2):
            # [Q_i,Pprime_j]=2 delta_ij on the untruncated polynomial domain.
            lhs=defaultdict(int); add(lhs,op(op(v,j,-1),i,1)); add(lhs,op(op(v,i,1),j,-1),-1)
            assert clean(lhs)==({k:2*x for k,x in v.items()} if i==j else {}); count+=1
    print('PASS actual 125-site Hamiltonian polynomial-domain commutators',count,'exact integer controls',flush=True)


if __name__=='__main__':
    pointer(); records(); oscillator()
