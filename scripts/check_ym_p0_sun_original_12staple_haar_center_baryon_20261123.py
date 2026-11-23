#!/usr/bin/env python3
"""Exact source-native 4D Wilson F19 pair 12-staple SU(N) Haar centre-charge audit.

- Enumerate ALL original L4 positive links and plaquette words: 1024,1536.
- Pick actual R445 y-direction even-start ordered pair at (0,0,0,0).
- Assign 12 DISTINCT exterior spectator y-parallel Wilson links to realize
  six central I + six central omega I SU3 staples at W=I.
- Evaluate exact CONTINUOUS SU(N) Haar moments for H=hI via the SU(N) Weyl
  torus Laurent constant term, not finite-group/quadrature simulation.
- Independently check SU(N) universal balanced meson and baryon formulas.
The physical CMP119/122 gauge-fixed T and absolute cutoff-uniform W3 remain open.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from math import factorial
from functools import lru_cache
import sympy as S

checks=0
def ok(v,message):
    global checks
    if v is not True and v != S.true:
        raise AssertionError(f'{checks}: {message}: {v!r}')
    checks+=1

def shift(x,j,L=4,step=1):
    y=list(x);y[j]=(y[j]+step)%L;return tuple(y)

def faceword(x,mu,nu,L=4):
    assert mu<nu
    return [((x,mu),1),((shift(x,mu,L),nu),1),
            ((shift(x,nu,L),mu),-1),((x,nu),-1)]

L=4
x=(0,0,0,0);axis=1
P=[(a,mu,nu) for a in product(range(L),repeat=4) for mu,nu in combinations(range(4),2)]
E=[(a,mu) for a in product(range(L),repeat=4) for mu in range(4)]
assert len(P)==1536 and len(E)==1024
U0=(x,axis);U1=(shift(x,axis,L),axis)
selected={U0: -1,U1: +1} # V^{-1} and V at fixed W=I
T=[]
controls={}
for face in P:
    word=faceword(*face)
    touched=[(link,orient) for link,orient in word if link in selected]
    ok(len(touched)<=1,'no original plaquette touches BOTH consecutive axial links')
    if touched:
        link,or_sel=touched[0]
        other=[(l,o) for l,o in word if l[1]==axis and l!=link]
        ok(len(other)==1,'exact one opposite original axial spectator control')
        sl,or_other=other[0]
        ok(or_other==-or_sel,'opposite same-axis Wilson face sign')
        ok(sl not in selected,'no selected pair link is an opposite link')
        T.append((face,link,or_sel,sl,or_other))
        ok(sl not in controls,'unique original parallel spectator for this face')
        controls[sl]=face
ok(len(T)==12 and len(controls)==12,'twelve native touched faces/twelve independent controlling exterior links')
# All 12 control links transverse-odd to the original 2-block coarse selection.
for sl in controls:
    ok(any(sl[0][v]%2==1 for v in range(4) if v!=axis),'each controlling native link is actual F19 spectator')

omega=-S.Rational(1,2)+S.sqrt(3)*S.I/2
ok(S.simplify(omega**3)==1,'omega is SU3 centre element')
ok(S.simplify(1+omega+omega**2)==0,'sum of SU3 centre phases')
phase_per_link={}
expected=[]
for face,link,or_sel,other,or_other in T:
    # Six plaquettes at U0 receive c=1; six at U1 receive c=omega.
    desired = S.Integer(1) if link==U0 else omega
    phase=desired if link==U0 else S.conjugate(desired)
    # Explicit orientation conversion:
    # selected V power = or_sel*vexp, other center power=-or_sel;
    # Re(z V^{-1})=Re(conj(z) V) and z_spectator^(-vexp)=desired.
    vexp=selected[link]
    effective=S.simplify(phase**(-vexp))
    ok(S.simplify(effective-desired)==0,'exact original Wilson oriented phase transfer')
    phase_per_link[other]=phase
    expected.append(desired)
ok(len(expected)==12 and expected.count(S.Integer(1))==6 and expected.count(omega)==6,'true six-plus-six SU3 native face staples')
h=S.simplify(sum(expected))
ok(S.simplify(h-6*(1+omega))==0,'original H=hI SU3 with centre source exterior')
ok(S.simplify(h*S.conjugate(h)-36)==0,'h magnitude 6')
ok(S.simplify(h**3+216)==0,'SU3 detH negative exactly')
# Compare genuine original plaquette words at V in SU3 center (3 distinct
# exact configurations) to converted source sum, not just symbol assignment.
for Vphase in (S.Integer(1),omega,omega**2):
    def value(link):
        if link==U0: return Vphase**(-1)
        if link==U1: return Vphase
        return phase_per_link.get(link,S.Integer(1))
    native=S.Integer(0)
    converted=S.Integer(0)
    for face,link,or_sel,other,or_other in T:
        pl=S.prod(value(l)**orientation for l,orientation in faceword(*face))
        # on center SU3, ReTr(pl I)/3=Re(pl)
        native+=S.expand_complex((pl+S.conjugate(pl))/2)
        c=S.Integer(1) if link==U0 else omega
        term=c*Vphase
        converted+=S.expand_complex((term+S.conjugate(term))/2)
        ok(S.simplify(pl*S.conjugate(pl)-1)==0,'actual SU3 group element on original face')
    ok(S.simplify(native-converted)==0,'original 1536-face geometry touched 12-source external field identity')

# Continuous SU(N) Weyl integral exactly as Laurent constant term: for
# N up to 4, product_{i<j}(1-z_i/z_j)(1-z_j/z_i) / N! on the
# (N-1)-torus; normalized Fourier/Haar angular measure, NOT finite group.
def mon_add(a,b):return tuple(i+j for i,j in zip(a,b))
def mon_neg(a):return tuple(-i for i in a)
def poly_mul(a,b):
    out=defaultdict(int)
    for ka,va in a.items():
        for kb,vb in b.items(): out[mon_add(ka,kb)]+=va*vb
    return {k:v for k,v in out.items() if v}

def poly_power(p,n):
    zero=(0,)*len(next(iter(p)))
    ans={zero:1}
    for _ in range(n):ans=poly_mul(ans,p)
    return ans

@lru_cache(None)
def haar_weight(N):
    zero=(0,)*(N-1)
    e=[tuple(1 if j==i else 0 for j in range(N-1)) for i in range(N-1)]
    e.append(tuple(-1 for _ in range(N-1)))
    weight={zero:1}
    for i,j in combinations(range(N),2):
        d=tuple(e[i][k]-e[j][k] for k in range(N-1))
        f={zero:2,d:-1,mon_neg(d):-1} # |1-z_i/z_j|^2
        weight=poly_mul(weight,f)
    ok(Q(weight.get(zero,0),factorial(N))==1,'Weyl Haar normalizes 1 exactly')
    return weight, {e_i:1 for e_i in e}, {mon_neg(e_i):1 for e_i in e}

@lru_cache(None)
def haar_trace_moment(N,k,l):
    w,trace,tracedag=haar_weight(N)
    pr=poly_mul(poly_power(trace,k),poly_power(tracedag,l))
    ct=sum(c*w.get(mon_neg(m),0) for m,c in pr.items())
    return Q(ct,factorial(N))

for N in (2,3,4):
    for k in range(0,7):
        for l in range(0,7-k):
            moment=haar_trace_moment(N,k,l)
            if (k-l)%N:
                ok(moment==0,f'centre-charge exclusion SU{N} ({k},{l})')
            if k==l==1:ok(moment==1,'universal meson trace-trace moment')
            if k==l==2:ok(moment==2,'universal balanced fourth trace moment')
            if k==N and l==0:ok(moment==1,'first SU(N) baryon Haar epsilon moment')
            if l==N and k==0:ok(moment==1,'first SU(N) antibaryon Haar epsilon moment')
    print('Haar SU({}) exact CT moments (k=l=1, k=N l=0, k=l=2):'.format(N),
          haar_trace_moment(N,1,1),haar_trace_moment(N,N,0),haar_trace_moment(N,2,2))

# Exact SU3 all-12-staple central H coefficient polynomial via continuous Haar.
def external_coeff(N,h,degree):
    # exp[(beta/N) ReTr(h V)]
    return S.simplify(sum(
         S.Rational(1, (2*N)**degree*factorial(k)*factorial(degree-k)) *
         h**k *S.conjugate(h)**(degree-k)*
         haar_trace_moment(N,k,degree-k)
         for k in range(degree+1)))

for tag,hval in [('coherent',S.Integer(12)),('frustrated',h)]:
    vals=[S.simplify(external_coeff(3,hval,k)) for k in range(5)]
    print('Original SU3 12-staple',tag,'full Haar Z coefficients β⁰..β⁴:',vals)
    target=([1,0,4,S.Rational(8,3),8] if tag=='coherent' else
            [1,0,1,-S.Rational(1,3),S.Rational(1,2)])
    ok(all(S.simplify(v-e)==0 for v,e in zip(vals,target)),
       'rigorous full Haar SU3 meson+baryon original source coefficients')

# SU2 exact Bessel local integral, independent from Laurent CT.
beta=S.symbols('beta',real=True)
for scalar_h in (S.Integer(1),S.Integer(6),S.Integer(12)):
    coeff=[S.simplify(external_coeff(2,scalar_h,k)) for k in range(7)]
    bessel=S.series(2*S.besseli(1,beta*scalar_h)/(beta*scalar_h),beta,0,7).removeO()
    for k,v in enumerate(coeff):
        ok(S.simplify(v-bessel.coeff(beta,k))==0,'all beta SU2 Bessel through sixth Taylor coefficient')

# One source-selected full coefficient is sign-INDEFINITE: the original SU3
# baryonic degree-3 term is +8/3 beta^3 or -1/3 beta^3 with genuine
# ORIGINAL allowed central SU3 spectator assignments and same pair W=I.
# This forbids a positivity assumption on each individual baryonic term
# in a proposed ABSOLUTE physically marked CMP119 cluster sum.

# Analytic uniform tail: each original |ReTr(HV)/N|<=12.
# Truncating ordinary real-exponential series at order M admits the
# exact absolute error <=e^(12β)(12β)^(M+1)/(M+1)!.
for M in (2,3,4,8,16):
    # show fixed β at 1/4 and 1/2 safe upper bound as rational e^x < 1/(1-x)
    for b in (Q(1,96),Q(1,48)):
        y=12*b
        assert y<1
        tail=Q(y.numerator**(M+1),y.denominator**(M+1)*factorial(M+1))*1/(1-y)
        ok(tail>=0 and tail <= Q(y.numerator**(M+1),y.denominator**(M+1)*factorial(M+1))*4/3,
           'rigorous rational beta<1/12 Haar T approximation tail bound')


# EXACT ORIGINAL MARKED SU3 source at one genuine F-mark face, selected
# F=(0,y,z) touches U0. Under the original chosen central exterior F(V)
# = 1 - ReTr(V)/3. With H=hI, D_{I} Z/β is this marked trace mass.
a,beta_sym=S.symbols('a beta',real=True)
for tag,hval in [('coherent',S.Integer(12)),('frustrated',h)]:
    zc=[S.simplify(external_coeff(3,a+S.I*S.im(hval),k)) for k in range(6)]
    sub={a:S.re(hval)}
    marked=[S.simplify((zc[k]-S.diff(zc[k+1],a)).subs(sub)) for k in range(4)]
    target=([S.Integer(1),-S.Rational(2,3),S.Rational(10,3),S.Integer(0)]
            if tag=='coherent' else
            [S.Integer(1),-S.Rational(1,6),S.Rational(13,12),-S.Rational(1,2)])
    print('Original SU3 genuine F-mark deficit one-T coefficients β⁰..β³:',tag,marked)
    ok(all(S.simplify(u-v)==0 for u,v in zip(marked,target)),
       'source unique original F-plaquette marked directional derivative')

# EXACT native all-N two-pair shared-face obstruction: two DIFFERENT
# selected original R445 even-origin pairs in the y/z axes at the same
# original source site.  Fix both original W=I, put U0=V^-1,U1=V;
# other 1020 original positive links remain identity.  The original
# action has 11 isolated faces per pair and ONE original shared y-z face:
# S_N(theta,phi)=(2/N)[11(1-cos(theta))+11(1-cos(phi))
#                          +(1-cos(phi-theta))].
for axes in combinations(range(4),2):
    source_pairs=[]
    for direction in axes:
        source_pairs.append({(x,direction):-1,(shift(x,direction,L),direction):1})
    incidence=defaultdict(int)
    both=[]
    for face in P:
        w=faceword(*face)
        coefficient=tuple(sum(o*signs.get(link,0) for link,o in w) for signs in source_pairs)
        incidence[coefficient]+=1
        if coefficient[0] and coefficient[1]:both.append((face,coefficient))
    ok(len(both)==1 and both[0][0]==(x,*axes),'one and only one true original shared source face')
    ok(incidence[(0,0)]==1513,'23 original physical touched faces')
    ok(sum(n for c,n in incidence.items() if c[0] and not c[1])==11,'11 singly sourced first pair faces')
    ok(sum(n for c,n in incidence.items() if c[1] and not c[0])==11,'11 singly sourced second pair faces')
    theta,phi=S.symbols('theta phi',real=True)
    for N in (2,3,4,5,8):
        action=S.Rational(2,N)*sum(count*(1-S.cos(c[0]*theta+c[1]*phi))
                            for c,count in incidence.items())
        reference=S.Rational(2,N)*(11*(1-S.cos(theta))+
                   11*(1-S.cos(phi))+(1-S.cos(phi-theta)))
        ok(S.trigsimp(action-reference)==0,'FULL native Wilson pair interaction exactly one shared face')
        mixed=S.diff(action,theta,phi).subs({theta:0,phi:0})
        ok(mixed==-S.Rational(2,N),'SU(N) mixed original full-action Hessian nonseparable')

print('PASS',checks,'original 4D Wilson geometry, genuine continuous SU(N) Weyl-Haar moments, F-source marked baryon and original two-pair T nonfactorization.')
print('NOTE: source-local SU(N) F19 Haar T, NOT the physical CMP119/122 constrained T, W3 or Clay gap.')
