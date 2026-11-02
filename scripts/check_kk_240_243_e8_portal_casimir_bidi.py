#!/usr/bin/env python3
"""240/243 role audit + E8-vs-ternary adjacency + KK Higgs portal gate.

PROVENANCE:
- DASHI PR #1094, T5E8RelativeComplementCandidateExact: cardinal 243=3+240,
  with NO E8 recognition or action intertwiner.
- E8 240 norm-two roots (classical root-system theorem; explicitly enumerated).
- DASHI PR #701, ideal-plate Casimir E/A=-pi²/(720d³),
  p=-pi²/(240d⁴), not the KK circle Casimir.
- DASHI PR #1241: selected free 5D QED+six vectorlike quarks+SU3 gluons
  produces stationarity D ~ -240 at b0=1e-24m.
- DASHI Physics/DarkSector/GaugeSingletPortal: singlet quadratic Higgs
  portal is operator-allowed, but has no fixed physical coupling or mass.

NO identification of unrelated 240 numbers; no proof of E8 mechanism,
general QCD, 5D Higgs action, portals, or observed physics.
"""
from collections import Counter
from itertools import combinations, product
from math import ceil
from mpmath import mp

mp.dps=43
states=list(product((-1,0,1),repeat=5))
diagonals={(t,)*5 for t in (-1,0,1)}
relative=[p for p in states if p not in diagonals]
assert len(states)==243 and len(diagonals)==3 and len(relative)==240
def path_adjacency(p,q): return sum(abs(a-b) for a,b in zip(p,q))==1
def circle_adjacency(p,q): return sum(a!=b for a,b in zip(p,q))==1
path_degree=Counter(sum(path_adjacency(p,q) for q in relative) for p in relative)
circle_degree=Counter(sum(circle_adjacency(p,q) for q in relative) for p in relative)
assert path_degree==Counter({5:40,6:70,7:80,8:50})
assert circle_degree==Counter({9:30,10:210})

# E8 standard 112 integral +/-e_i +/-e_j and 128 half-integral
# (even number negative) roots. Coordinates doubled for exact ints.
roots=[]
for i,j in combinations(range(8),2):
    for a,b in product((-2,2),repeat=2):
        v=[0]*8;v[i]=a;v[j]=b;roots.append(tuple(v))
for v in product((-1,1),repeat=8):
    if sum(t==-1 for t in v)%2==0: roots.append(v)
assert len(roots)==len(set(roots))==240
assert all(sum(t*t for t in r)==8 for r in roots)
e8_degree=Counter(
    sum(sum(a*b for a,b in zip(u,v))==4 for v in roots) for u in roots
)
assert e8_degree==Counter({56:240})
assert max(path_degree)<56 and max(circle_degree)<56
print('PASS ternary relative carrier: 243=3 diagonal +240 non-diagonal')
print('P3^5 induced adjacency degrees:',dict(sorted(path_degree.items())))
print('C3^5 induced adjacency degrees:',dict(sorted(circle_degree.items())))
print('E8 norm-two, inner-product-one root graph degrees:',dict(e8_degree))
print('PASS NO adjacency-preserving bijection for these selected graph operators')

# Classical ideal-plate Casimir: differentiate SAME energy.
import sympy as sp
d=sp.symbols('d',positive=True)
energy=-sp.pi**2/(720*d**3)
plate_pressure=-sp.diff(energy,d)
assert sp.simplify(plate_pressure+sp.pi**2/(240*d**4))==0
assert 3*240==720 and 3+240==243
print('PASS plate 720->240 is inverse-cube derivative, unrelated to E8 count')

# QCD in the selected 5D free periodic S1, b0 = 1e-24m,
# same fixed radius, trivial Wilson phases, vectorlike periodic quarks.
Z5=mp.zeta(5)
hbarc=mp.mpf('0.1973269804e-15') # GeV*m
b0=mp.mpf('1e-24')/hbarc
masses=(mp.mpf(x) for x in ('.00216','.00470','.0935','1.273','4.183','172.56'))
qs=[2*mp.pi*m*b0 for m in masses]
def f(z):
    if z==0: return mp.mpf(1)
    e=mp.exp(-z)
    return (mp.polylog(5,e)+z*mp.polylog(4,e)+z*z*mp.polylog(3,e)/3)/Z5
def fp(z):
    if z==0: return mp.mpf(0)
    e=mp.exp(-z)
    return -z*(mp.polylog(3,e)+z*mp.polylog(2,e))/(3*Z5)
def h(z):
    return f(z)-z*fp(z)/5
# For real nonnegative portal mass z=2pi m_S b0, each periodic REAL
# bosonic degree changes D=W'-5W by +5h(z); 0<h(z)<=1.
def hp(z):
    if z==0: return mp.mpf(0)
    e=mp.exp(-z)
    return -z*(3*mp.polylog(3,e)+3*z*mp.polylog(2,e)+
               z*z*mp.polylog(1,e))/(15*Z5)
for z in [mp.mpf(x) for x in ('0','.00001','.5','2','10')]:
    assert 0<h(z)<=1
    if z>0:
        assert hp(z)<0
        assert abs(mp.diff(h,z)-hp(z))<mp.mpf('1e-35')
# eight SU3 vector bosons (3 each) and six quark flavours x three colours
# x four Dirac fermion units. Only this selected free 5D spectrum.
deltaW=-24+12*mp.fsum(f(z) for z in qs)
deltaWp=12*mp.fsum(z*fp(z) for z in qs)
D=deltaWp-5*deltaW
assert mp.mpf('-240')<D<mp.mpf('-239.999999')
n_min=ceil(float(-D/5))
assert n_min==48 and 47*5<(-D)
# Portal scalar with Higgs-sourced effective mass is one *real* scalar:
# count 1 unit if S is uncondensed and mass does NOT depend on radius.
# A complex singlet would be 2 units (two independent real degrees).
for mass in (0,86,125,1e5):
    z=2*mp.pi*mp.mpf(mass)*b0
    shifted=D+5*h(z)
    assert shifted<mp.mpf('-234.9')
    print(f'one real Z2 Higgs portal, m_eff={mass}GeV, '
          f'D_after={mp.nstr(shifted,18)}')
assert D+2*5<0 # one complex scalar also insufficient
assert D+4*5<0 # even four light Higgs real scalar modes alone insufficient
# 48 separately added free, periodic real bosons CAN satisfy
# D+48*5*h(z)=0 when their common z is tuned; no physical realization.
target=-D/240
assert 0<target<1
lo,hi=mp.mpf(0),mp.mpf('0.01')
for _ in range(110):
    mid=(lo+hi)/2
    if h(mid)>target: lo=mid
    else: hi=mid
z48=(lo+hi)/2
assert abs(D+240*h(z48))<mp.mpf('1e-28')
m48=z48/(2*mp.pi*b0)
print('selected QED+QCD D=',mp.nstr(D,22))
print('restricted free-real-scalar DOF minimum=',n_min,
      '48-scalar degenerate mass in GeV=',mp.nstr(m48,15))

# E6 trinification physical DONOR, not an identified E8 theory:
# E6 adjoint under SU3^3: 78=(8+8+8)+27+27.
# E8 under E6 x SU3: 248=(78+8)+(27*3)+(27*3).
# If the first SU3^3 factor is SU3_colour, TWO additional unbroken
# SU3 vector octets have 2*8*3=48 massless 5D vector polarizations.
# Their free KK Casimir sign is -48 and the D shift +5*48=+240.
# This balances the +48 light-quark/gluon net *massless-limit* count.
# It does NOT imply E8 roots, hypercharge, chirality, or collider validity.
assert 78==8+8+8+27+27
assert 248==78+8+27*3+27*3
assert 248-8==240
extra_vector_generators=2*8
extra_vector_polarizations=extra_vector_generators*3
assert extra_vector_polarizations==48
assert delta + 5*extra_vector_polarizations>0
assert delta+5*extra_vector_polarizations<mp.mpf('1e-6')
# The same free-field normalisation that tuned 48 real bosons at 86GeV
# also tunes sixteen vectors, since 16*3=48 Casimir polarizations.
assert abs(delta+5*extra_vector_polarizations*h(z48))<mp.mpf('1e-28')
print('E6->SU3^3 gauge adjoint=24 +54; E8->E6xSU3 adjoint=86+162=248')
print('TWO extra SU3 octets -> 16 5D vectors = 48 free bosonic units')
print('massless-limit residual after these vectors:',
      mp.nstr(delta+240,17))
print('FORMAL scalar-like 48-unit effective mass, NOT a valid 5D vector mass GeV:',
      mp.nstr(m48,15))
print('FAIL Higgsed 5D vector reinterpretation: 4 massive rather than 3 massless polarizations')
print('FAIL full physical trinification: mass generation, Higgs sector, '
      'EW chirality, interaction loops and visible-vector bounds not paid')

print('PASS portal 1 or 2 scalar DOF cannot rescue same-radius vacuum')
print('NOTE if Higgs vev, portal mass or boundary data depend on radion, '
      'new terms enter D: rerun with a single consistent 5D action')
print('LIMIT MMP 1+1 optical Dirac circle Casimir, plate Casimir, '
      'KK 5D S1 and E8 lattice have distinct consumers')
