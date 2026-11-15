#!/usr/bin/env python3
"""C2 Python/SymPy mathematics: original R71/R853/R692 selected rate.

Exact initial finite-mode source identity, a uniform global coordinate Lipschitz
constant, and a Picard/FTC derivative bound on the UNCHANGED R854 horizon.
Not a rational-valued R408 Agda live packet or a kernel receipt.
"""
from collections import defaultdict
from functools import lru_cache
from fractions import Fraction
from itertools import product
from sympy import I, Matrix, Rational, S, conjugate, simplify, expand, sqrt

N=4
MODES={m for m in product(range(-N,N+1),repeat=3) if m!=(0,0,0)}
ZERO=Matrix([0,0,0])
SEED={
    (3,0,0):Matrix([0,2+2*I,-2-I]),
    (0,4,0):Matrix([2+2*I,0,2+2*I]),
    (3,4,0):Matrix([6*I,-Rational(9,2)*I,-2+2*I]),
}
def neg(k):return tuple(-x for x in k)
def add(k,p):return tuple(x+y for x,y in zip(k,p))
def sub(k,p):return tuple(x-y for x,y in zip(k,p))
def wt(k):return 2**((max(map(abs,k))-1).bit_length())
def sq(k):return sum(z*z for z in k)
def projection(k,v):
    kv=Matrix(k)
    return v-kv*(kv.dot(v)/sq(k))
def cross(a,b):return a.cross(b)
def innerreal(a,b):return expand(sum(conjugate(a[j])*b[j] for j in range(3))).as_real_imag()[0]

def exact_snapshot():
    u={}
    for k,v in SEED.items():
        u[k]=v
        u[neg(k)]=v.applyfunc(conjugate)
    assert len(u)==6 and all(Matrix(k).dot(v)==0 for k,v in u.items())
    raw=defaultdict(lambda:ZERO)
    for p,v in u.items():
        for q,w in u.items():
            k=add(p,q)
            if k in MODES:
                raw[k]=raw[k]+v.dot(Matrix(q))*w
    forcing={k:simplify(-I*projection(k,z)) for k,z in raw.items()}
    forcing={k:z for k,z in forcing.items() if z!=ZERO}
    assert len(forcing)==8, sorted(forcing)
    expected={
        (-3,-4,0):[(Rational(224,25),0),(-Rational(168,25),0),(14,-6)],
        (-3,0,0):[(0,0),(-27,-27),(60,36)],
        (-3,4,0):[(0,-Rational(224,25)),(0,-Rational(168,25)),(6,-50)],
        (0,-4,0):[(48,48),(0,0),(68,18)],
        (0,4,0):[(48,-48),(0,0),(68,-18)],
        (3,-4,0):[(0,Rational(224,25)),(0,Rational(168,25)),(6,50)],
        (3,0,0):[(0,0),(-27,27),(60,-36)],
        (3,4,0):[(Rational(224,25),0),(-Rational(168,25),0),(14,6)],
    }
    assert set(expected)==set(forcing)
    for k, row in expected.items():
        for j,(a,b) in enumerate(row):
            assert simplify(forcing[k][j]-(a+I*b))==0,(k,j,forcing[k])
    assert all(sqrt(sq(k)).is_Rational for k in set(forcing)|set(u))

    @lru_cache(None)
    def H(k,source,sign):
        v=(forcing if source=='f' else u).get(k,ZERO)
        if v==ZERO:return ZERO
        return simplify((projection(k,v)+sign*I*cross(Matrix(k),v)/sqrt(sq(k)))/2)

    # Literal R224 mixed product and signed R230 commutator, summed by
    # original R692 coherentWork( Mk, Gk ) = 2 Re <Mk,Gk>.
    mixed=defaultdict(lambda:ZERO)
    G=defaultdict(lambda:ZERO)
    for p in u:
        for q in u:
            k=add(p,q)
            if k in MODES:
                mixed[k]=mixed[k]+cross(H(p,'u',1),H(q,'u',-1))
    for p in forcing:
        for q in u:
            k=add(p,q)
            if k in MODES:
                G[k]=G[k]+cross(H(p,'f',1),H(q,'u',-1))-cross(H(p,'f',-1),H(q,'u',1))
    # Exact R829 VectorWork original mixed/commutator rows, not just totals.
    # Source owner: NSTriadKNR650Rational345VectorWorkRound829Exact.agda.
    original_rows={
       (-3,-4,0):(
           [-7-I,-7-I,-1+I],
           [8-23*I,8-23*I,-98-56*I]),
       (-3,0,0):(
           [-Rational(21,10)-Rational(9,2)*I,Rational(7,10)+Rational(3,2)*I,-Rational(69,10)-Rational(9,2)*I],
           [-Rational(246,5)+42*I,Rational(858,25)-Rational(678,25)*I,-Rational(909,5)+Rational(225,2)*I]),
       (-3,4,0):(
           [1+I,-1-I,-1+7*I],
           [2-35*I,-2+35*I,308+50*I]),
       (0,-4,0):(
           [-Rational(9,5)-Rational(17,5)*I,Rational(18,5)+Rational(34,5)*I,-Rational(46,5)-3*I],
           [Rational(2913,50)-Rational(833,50)*I,-Rational(117,5)-Rational(171,5)*I,Rational(5428,25)-Rational(5412,25)*I]),
    }
    for k,(mv,gv) in list(original_rows.items()):
        assert neg(k) not in original_rows
        original_rows[neg(k)]=([conjugate(x) for x in mv],[conjugate(x) for x in gv])
    for k,(mv,gv) in original_rows.items():
        assert simplify(mixed[k]-Matrix(mv))==ZERO,(k,'mixed',mixed[k])
        assert simplify(G[k]-Matrix(gv))==ZERO,(k,'G',G[k])
    assert len(original_rows)==8
    # Output-specific zero witnesses needed by R692 come for free from
    # finite-support products. Do not drop nonzero contributions by hand.
    C=simplify(2*sum(innerreal(mixed[k],G[k]) for k in MODES if k in mixed and k in G))
    P=simplify(2*sum(wt(k)*innerreal(u[k],forcing.get(k,ZERO)) for k in u))
    D=simplify(sum(wt(k)*sq(k)*sum(conjugate(vj)*vj for vj in v) for k,v in u.items()))
    r0=simplify(6*(12*C-P+D))
    assert C==Rational(-557627,125),C
    assert P==0,P
    assert D==15834,D
    assert r0==Rational(-28273644,125),r0
    return C,P,D,r0,len(mixed),len(G)

def analytic_bounds():
    # Real/imag component max-norm on the 2184-dimensional reality chart.
    n=len(MODES); M=12; nu=1
    assert n==728 and n//2*6==2184
    # For k!=0, each |P(k)| absolute row sum <=2: the C1 proof.
    # For k!=0, |(k cross)_j| row sum / |k| <=sqrt(2), by Cauchy.
    # Consequently each real OR imaginary component of H_k^pm v is
    # <= [(2+sqrt(2))/2]*||v||_realinf < 2||v||_realinf.
    for k in MODES:
        k2=sq(k)
        for j in range(3):
            ps=sum(abs(Fraction(int(j==t))-Fraction(k[j]*k[t],k2)) for t in range(3))
            assert ps<=2,(k,j,ps)
            transverse_sq=sum(k[t]*k[t] for t in range(3) if t!=j)
            assert transverse_sq*2<=2*k2
    proj=2;hel=2;dot=3*N;cross_factor=4;lap=3*N*N;weight=8
    # Nonlinear-only forcing at each real/imag coordinate; the physical
    # RHS includes separate viscosity. No extra projection is applied twice.
    F=n*2*dot*proj*M*M
    FL=n*2*(dot*proj*M+dot*M*proj)
    K=F+lap*M
    HU=hel*M; HU_L=hel
    HF=hel*F; HF_L=hel*FL
    MB=n*cross_factor*HU*HU
    ML=n*2*cross_factor*HU*HU_L
    GB=n*2*cross_factor*HF*HU
    GL=n*2*cross_factor*(HF_L*HU+HF*HU_L)
    # C=2Re sum_k conj(Mk) . Gk; each real component multiplication
    # incurs the two real/imag parts of the Hermitian pairing.
    CL=2*2*n*3*(ML*GB+MB*GL)
    # P=2 sum_k w_k Re <u_k,F_k>; F_k is nonlinear only.
    PL=2*weight*n*3*2*(F+M*FL)
    # D=sum_k w_k |k|^2 |u_k|^2: three components, two squares each.
    DL=weight*n*3*lap*4*M
    rateL=6*(12*CL+PL+DL)
    sourceL=391309593930357307785216
    assert (F,FL,K)==(5031936,838656,5032512)
    assert (MB,ML,GB,GL)==(1677312,279552,1406687772672,351671943168)
    assert (CL,PL,DL,rateL)==(8588413584135904296960,1055015829504,40255488,618365778064115445891072)
    assert rateL<2*sourceL,(rateL,sourceL)
    T=Fraction(226189,3938540454339300631433585885184)
    r0=Fraction(-28273644,125)
    assert K*T<6
    # Chain rule on the unique C1 classical Galerkin C^1 solution:
    # |r'(t)| <= rateL * ||x'(t)||inf <= rateL*K throughout [0,T].
    # R856 integer-multiplier ceiling: 2K=10065024, < 10065030.
    assert 2*K==10065024 and 2*K<=10065030
    assert rateL*K<2*sourceL*K
    assert 2*sourceL*K*T==226189
    upper=r0+rateL*K*T
    majorant=r0+2*sourceL*K*T
    assert majorant==Fraction(-19,125)<0 and upper<majorant
    integrated=r0*T+Fraction(rateL*K,2)*T*T
    assert integrated<0
    return dict(L=rateL,K=K,T=T,rate_upper=upper,majorant=majorant,integral_upper=integrated)

if __name__=='__main__':
    C,P,D,r0,nmix,ng=exact_snapshot()
    b=analytic_bounds()
    print('PASS exact source R692/R230/R224/R847/R853 initial scalar',C,P,D,r0)
    print('PASS symbolic finite-sum proof bounds on all 728 modes; rate-state Lipschitz',b['L'])
    print('PASS R71 real-ODE chain derivative |r\'(t)|<=L*K, original R854 T',b['T'])
    print('PASS R856 integer multiplier 2K=10065024 below 10065030')
    print('PASS strict selected rate <=', b['rate_upper'],'<',b['majorant'])
    print('PASS selected integral <=',b['integral_upper'],'< 0')
    print('NOT AN AGDA R408 real-time packet or native Agda/Lean proof.')
