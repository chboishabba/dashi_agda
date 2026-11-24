#!/usr/bin/env python3
"""Exact source R231/R236: rational Pythagorean helical input modes,
Leray-transverse physical output, active strict deep-FL, 4 actual cells,
and universal full-cutoff spectator mean / leading 32||M||^2 C^5.
No original NSE-in-time or Agda 2.9 kernel acceptance is implied.
"""
from itertools import product
from sympy import Matrix,I,Rational as Q, symbols, simplify, expand, sqrt, re, im

K=(83,64,0)
PAIRS=[((0,64,0),(83,0,0)), ((3,4,0),(80,60,0)),
       ((20,48,0),(63,16,0)), ((35,0,0),(48,64,0))]
T=symbols('t',real=True)

def helical(k):
    a,b,c=k
    assert c==0 and a*a+b*b>0
    d=sqrt(a*a+b*b)
    assert d.is_Integer  # LITERAL rational Euclidean norm, unlike sqrt2 examples
    ex=Matrix([Q(a,d),Q(b,d),0]); vy=Matrix([Q(-b,d),Q(a,d),0]); ez=Matrix([0,0,1])
    plus=vy+I*ez; minus=vy-I*ez
    assert simplify(I*ex.cross(plus)-plus)==Matrix([0,0,0])
    assert simplify(I*ex.cross(minus)+minus)==Matrix([0,0,0])
    assert simplify(ex.dot(plus))==simplify(ex.dot(minus))==0
    return plus,minus

def shell(mode):
    m=max(map(abs,mode))
    return 0 if m<=1 else (m-1).bit_length()
def r236(p,q,k=K):
    a,b,j=map(shell,(p,q,k))
    if a+3<b:return 'FL' if 3*a<=2*b else 'CC'
    if b+3<a:return 'FL' if 3*b<=2*a else 'CC'
    if j+3<a and j+3<b:return 'HH' if 5*j<=4*max(a,b) else 'CC'
    return 'CC'

def full_geometry(C,k):
    if isinstance(C,int) and all(isinstance(d,int) for d in k):
        assert C>=max(map(abs,k))
    side=[2*C-abs(t)+1 for t in k]
    size=side[0]*side[1]*side[2]
    avg=Q(1,2)*sum(x*x for x in k)+Q(1,6)*sum(m*m-1 for m in side)
    return size,avg

def check_small_direct_geometry():
    seen=0
    for C in range(1,5):
        for k in product(range(-C,C+1),repeat=3):
            limits=[(max(-C,d-C),min(C,d+C)) for d in k]
            count=0;total=0
            for px,py,pz in product(*(range(a,b+1) for a,b in limits)):
                p=(px,py,pz);q=tuple(k[i]-p[i] for i in range(3))
                assert all(-C<=d<=C for d in p+q)
                count+=1;total+=sum(x*x for x in p)+sum(x*x for x in q)
            n,mu=full_geometry(C,k)
            assert count==n and total==n*mu
            seen+=1
    return seen

def check_original_source():
    A=[];rates=[]
    for p,q in PAIRS:
        assert tuple(p[i]+q[i] for i in range(3))==K
        hp,_=helical(p);_,hm=helical(q)
        cell=simplify(hp.cross(hm));A.append(cell)
        rates.append(sum(v*v for v in p+q))
    assert rates==[10985,10025,6929,7625]
    assert [r236(*pair) for pair in PAIRS]==['CC','FL','CC','CC']
    plus={p for p,q in PAIRS};minus={q for p,q in PAIRS}
    plus|={tuple(-x for x in p) for p in tuple(plus)}
    minus|={tuple(-x for x in q) for q in tuple(minus)}
    # For the real field, u(-k) is the conjugate and remains in same +/- helicity
    # eigenspace; no additional cross cell hits output K.
    assert {(p,q) for p in plus for q in minus if tuple(p[i]+q[i] for i in range(3))==K}==set(PAIRS)
    a,b,c=symbols('a b c',real=True)
    coeff=[a,b,c,T]
    M=sum((d*v for d,v in zip(coeff,A)),Matrix([0,0,0]))
    equations=[im(M[0]),im(M[1]),re(M[2])-1]
    from sympy import solve
    solutions=solve(equations,[a,b,c])
    assert solutions=={a:Q(64,15)*T-Q(5,4),b:Q(25,28),c:-Q(13,3)*T}
    coefficients=[simplify(x.subs(solutions)) for x in coeff]
    M=simplify(M.subs(solutions))
    assert M==Matrix([0,0,1])
    assert Matrix(K).dot(M)==0 # genuine nonzero physical Leray output
    W=[simplify(2*re(M.dot(vec*co))) for vec,co in zip(A,coefficients)]
    assert W==[Q(5,2)-Q(128,15)*T,-Q(1,2),Q(104,15)*T,Q(8,5)*T]
    assert simplify(sum(W)-2)==0
    V=simplify(sum(r*w for r,w in zip(rates,W)))
    assert V==22450-Q(167488,5)*T
    assert W[1]!=0 # exact source deep-FL work = -1/2
    chosen=Q(-1,4)
    Vfixed=V.subs(T,chosen)
    assert Vfixed==Q(154122,5)
    for C,expected in [(83,-Q(33634973008,5)),(100,Q(73504991408,5))]:
        n,mu=full_geometry(C,K)
        S=n*(2*mu-Vfixed)
        assert S==expected
        print('cutoff',C,'source vertices',n,'total-rate',n*mu,'signed S',S)
        assert Vfixed==2*mu-S/n # BIDI original physical rate-work recovery
    # Fixed M and cutoff also allow S(t) to vary across both signs.
    n,mu=full_geometry(83,K)
    assert (n*(2*mu-V)).diff(T) != 0
    sx,sy,sz=symbols('sx sy sz',integer=True,nonnegative=True)
    C=symbols('C',integer=True,positive=True)
    k=(sx,sy,sz)
    nC,muC=full_geometry(C,k)
    # n(C)=8 C³+O(C²), mean rate=2 C²+O(C) for any fixed k.
    assert expand(nC).coeff(C,3)==8
    assert expand(muC).coeff(C,2)==2
    assert expand(nC*(2*muC-Vfixed)).coeff(C,5)==32
    print('PASS helical rational Fourier constructor, source-real conjugates, strict deep-FL and Leray P_k M=M')
    print('PASS cutoff BIDI and general 3-axis spectator polynomial: S(C)=32||M||² C^5+O(C^4) for W=2||M||²')
    return Vfixed

if __name__=='__main__':
    V=check_original_source()
    cases=check_small_direct_geometry()
    print('PASS direct independent rectangular source lattice sums',cases,'cutoff-output cases; fixed physical V',V)
    print('FIREWALL: original time-integrated R568 signed cutoff budget, Agda and P!=NP remain unproved')
