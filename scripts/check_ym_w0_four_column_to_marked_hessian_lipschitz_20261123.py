#!/usr/bin/env python3
"""W0->W1 exact four-column source-approximation stability, NOT W3/OS.

Local: python scripts/check_ym_w0_four_column_to_marked_hessian_lipschitz_20261123.py
Uses existing full original L4 Wilson ten-active-link Z2 centre *slice* owner;
never represents this slice as continuous SU(N) Haar or physical CMP119 T.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import importlib.util
import sympy as S

r=Q(9,100)
lam=Q(1519,2500)                # original Wilson deficits J_F,J_G in [0,2]
assert lam==1-4*r-4*r*r and lam>0
checks={"symbolic":0,"original_wilson":0,"approximation":0,"complex":0,"negative_controls":0}

a,b,c,d,s,t,da,db,dc,dd=S.symbols('a b c d s t da db dc dd')
K=a+b*s+c*t+d*s*t
M=a*d-b*c
assert S.expand(d*K-S.diff(K,s)*S.diff(K,t)-M)==0
checks['symbolic']+=1
Delta=da+db*s+dc*t+dd*s*t
Dp=(a+da)*(d+dd)-(b+db)*(c+dc)-M
assert S.expand(Dp-(d*da+a*dd+da*dd-b*dc-c*db-db*dc))==0
checks['symbolic']+=1
assert S.simplify((M+Dp)/(K+Delta)**2-M/K**2-(Dp/(K+Delta)**2+M*(1/(K+Delta)**2-1/K**2)))==0
checks['symbolic']+=1


def evalK(v,x,y):
    a,b,c,d=v
    return a+x*b+y*c+x*y*d

def det(v):
    a,b,c,d=v
    return a*d-b*c

def H(v,x,y):
    return det(v)/evalK(v,x,y)**2

def from_trace_to_deficit(v):
    # Existing source owner uses trace marks T_F,T_G in {-1,+1}.
    # The literal original deficit marks are J_F=1-T_F, J_G=1-T_G.
    a,tf,tg,tftg=v
    return (a,a-tf,a-tg,a-tf-tg+tftg)

def cone(v):
    a,b,c,d=v
    return (a>0 and 0<=b<=2*a and 0<=c<=2*a
            and max(Q(0),2*b+2*c-4*a)<=d<=min(2*b,2*c))

def uniform_bound(eps0,epsf,epsg,epsfg):
    """Proved bound for any real/complex |s|,|t|<=9/100.

    Original positive K0=a, 0<=F,G<=2, |cov(F,G)|<=1.
    Approximate four coefficients obey |Delta_j|<=eps_j*a.
    """
    e=eps0+r*(epsf+epsg)+r*r*epsfg
    D=4*eps0+epsfg+eps0*epsfg+2*(epsf+epsg)+epsf*epsg
    assert 0<=e<lam
    return D/(lam-e)**2 + e*(2*lam-e)/(lam*lam*(lam-e)**2)

def origin_bound(eps0,epsf,epsg,epsfg):
    D=4*eps0+epsfg+eps0*epsfg+2*(epsf+epsg)+epsf*epsg
    assert eps0<1
    return D/(1-eps0)**2 + eps0*(2-eps0)/(1-eps0)**2

# The original Wilson finite cut is imported rather than reimplemented.
p=Path(__file__).with_name('check_ym_p0_original_wilson_marked_ordered_t_20261123.py')
if not p.exists():
    raise FileNotFoundError(f'Original Wilson source checker is required in same scripts directory: {p}')
spec=importlib.util.spec_from_file_location('_ym_original_marked_T',p)
original=importlib.util.module_from_spec(spec)
spec.loader.exec_module(original)
assert (len(original.sites),len(original.links),len(original.faces))==(256,1024,1536)
assert len(original.selected)==128 and len(set(original.links)-original.selected)==896
V=[from_trace_to_deficit(original.flat)] + [from_trace_to_deficit(original.by_w[k]) for k in sorted(original.by_w)]
assert len(V)==5
for v in V:
    assert cone(v)
    a,b,c,d=v
    assert abs(det(v))<=a*a
    checks['original_wilson']+=2
    for x,y in product((-r,Q(0),r),repeat=2):
        assert evalK(v,x,y)>0
        assert evalK(v,x,y)>=lam*a
        assert S.Rational(evalK(v,x,y).numerator,evalK(v,x,y).denominator)>0
        checks['original_wilson']+=3

# All four coefficient errors are independently controlled relative to TRUE K0.
# These are synthetic CMP119 candidate perturbations, not physical source T.
for v in V:
    a=v[0]
    for epsilon in (Q(0),Q(1,1000),Q(1,100),Q(1,50)):
        B=uniform_bound(epsilon,epsilon,epsilon,epsilon)
        B0=origin_bound(epsilon,epsilon,epsilon,epsilon)
        for signs in product((-1,1),repeat=4):
            vp=tuple(v[i]+signs[i]*epsilon*a for i in range(4))
            assert abs(H(vp,Q(0),Q(0))-H(v,Q(0),Q(0)))<=B0
            checks['approximation']+=1
            for x,y in product((-r,Q(0),r),repeat=2):
                assert evalK(vp,x,y)>0
                err=abs(H(vp,x,y)-H(v,x,y))
                assert err<=B
                checks['approximation']+=2

# Certified complex-grid checks on the holomorphic two-source logarithmic germ.
# Bound is derived from triangle inequalities, not inferred from this finite grid.
for v in V:
    av=v[0]
    vv=tuple(S.Rational(x.numerator,x.denominator) for x in v)
    for x,y in product((S.Rational(9,100),-S.Rational(9,100),S.I*S.Rational(9,100),-S.I*S.Rational(9,100)),repeat=2):
        kk=vv[0]+x*vv[1]+y*vv[2]+x*y*vv[3]
        assert S.simplify(S.re(kk)**2+S.im(kk)**2-S.Rational(lam.numerator,lam.denominator)**2*vv[0]**2).is_nonnegative is True
        checks['complex']+=1

# Crucial negative control: even exact 1/F/G marginal columns (and cone membership)
# do not fix FG, and fixed, distance-independent error does NOT give spatial decay.
base=(Q(1),Q(1),Q(1),Q(1))   # independent F,G in {0,2} fair corner distribution
for epsilon in (Q(1,10000),Q(1,1000),Q(1,100),Q(1,10)):
    candidate=(Q(1),Q(1),Q(1),Q(1)+epsilon)
    assert cone(base) and cone(candidate)
    assert base[:3]==candidate[:3]
    assert H(base,Q(0),Q(0))==0 and H(candidate,Q(0),Q(0))==epsilon
    assert abs(H(candidate,Q(0),Q(0))-H(base,Q(0),Q(0)))<=origin_bound(Q(0),Q(0),Q(0),epsilon)
    checks['negative_controls']+=4

print('PASS',S.__version__,checks,'TOTAL',sum(checks.values()))
print('uniform domain |s|,|t|<=9/100; lambda=',lam)
print('exact source: native L4 full 1536-plaquette Wilson action on SU2-centre 10-link slice')
print('5 exact 1/JF/JG/JFJG source densities: global plus four fixed coarse F19 fibres')
print('4 independent approximate CMP119 column-error controls; 16 perturbation corners each')
print('OPEN: literal physical continuous SU(N) CMP119 T identity; termwise ABSOLUTE W3; cutoff-uniform decay; OS and Clay')
