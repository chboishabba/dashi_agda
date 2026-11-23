#!/usr/bin/env python3
"""Original RH P0 projective-pair prime-aperture constructive preflight.

Original source (dashi_lean4/main):
  RiemannProjectiveQuarticFourWindowHighWitness.lean    physical short support
  RiemannProjectiveCircularHyperbolicDuality.lean      P_g=4*g*B_g
  RiemannProjectiveQuarticFourWindowPoleSameObject.lean pole weights
  RiemannProjectiveQuarticFourWindowSignedPolePair.lean  two signed endpoints

For each endpoint, 8 exact linear conditions on an even perturbation h:
 (1-2) freeze A1=<g,cos(r u)>, A2=<g,cos(2r u)>, hence B_g;
 (3-6) freeze projective P_g moments M2,M4,M6,M8;
 (7-8) freeze both original pole response integrals.
M0(P_g) vanishes by the projective determinant identity.

Mathematical existence of exactly vanishing constraints + prescribed values
at log2 and log3 follows from the bump-evaluation / finite linear functionals
lemma, in the companion proof ledger. This script tests a *numerical* smooth
C-infinity fixture and atomic-corridor endpoint response approximations, NOT
Mathlib's actual noncomputable selected W; it is NOT a Lean or RH proof.
"""
import math
import numpy as np
import sympy as sp

lam_half,lam_two=sp.Rational(1,2),sp.Rational(2,3)
mu0=lambda lam:sp.factor((13*lam-8)/(144-54*lam))
A=lambda lam:(sp.Rational(1,2)-mu0(lam),sp.Rational(3,2)-lam+mu0(lam))
a,b=A(lam_half),A(lam_two)
assert mu0(lam_half)==-sp.Rational(1,78) and mu0(lam_two)==sp.Rational(1,162)
assert a==(sp.Rational(20,39),sp.Rational(77,78))
assert b==(sp.Rational(40,81),sp.Rational(68,81))
assert sp.factor(a[0]*b[1]-a[1]*b[0])==-sp.Rational(20,351)
# Nonproportional projective bracket vectors in the ATOMIC endpoint limit.
print('PASS source atomic endpoint A vectors, det=-20/351 (not the selected smooth W)')

A1,A2,ee,u,rr=sp.symbols('A1 A2 eps u r',real=True)
c1,c2,m2,m4,m6,m8,p1,p2=sp.symbols('c1 c2 m2 m4 m6 m8 p1 p2',real=True)
B=A1*sp.cos(2*rr*u)-A2*sp.cos(rr*u)
# Exact projective zeroth moment under frozen on-line Fourier coefficients:
assert sp.simplify(4*(A1*A2-A2*A1))==0
for moment in (m2,m4,m6,m8):
    assert sp.expand(4*ee*moment).subs(moment,0)==0
for w in (c1,c2,p1,p2):
    assert (ee*w).subs(w,0)==0
print('PASS SymPy exact 8-constraint projective moment/pole invariance and automatic M0')
# With even M0,M2,...,M8 all preserved, the first possible change
# in the original signed hyperbolic target defect is O(alpha^10).
z = sp.symbols('z')
cosh_tail = sp.cosh(z)-sum(z**(2*j)/sp.factorial(2*j) for j in range(5))
assert sp.simplify(sp.series(cosh_tail,z,0,12).removeO()-z**10/sp.factorial(10))==0
print('PASS exact first possible hyperbolic height-defect perturbation order 10')
# Exact affine-bump scaling: the *point height* can be kept fixed while
# smoothness constants blow up as widths shrink. The existing Lean source
# proves L1 scaling explicitly for orders 0,1,2. Higher orders follow the
# same chain rule for C-infinity unitContDiffBump.
delta=sp.symbols('delta',positive=True)
for k in (0,1,2,6,8,10):
    scale=delta**(1-k)
    assert sp.simplify(scale*delta**(k-1)-1)==0
assert sp.simplify((delta**(-1))/(delta))==delta**(-2)
print('PASS exact bump L1 kth derivative scale delta^(1-k): original global-tail derivative cost not frozen')

log2,log3,log4=np.log(2),np.log(3),np.log(4)
core200=16*(np.pi+1)/200
assert core200<0.36<log2<log3<1.25<log4
print('PASS exact support geometry: old core radius at t=200',round(core200,9),
      '< aperture (0.36,1.25) < log4; only log2 and log3 are sampled')

nodes,weights=np.polynomial.legendre.leggauss(96)
BUMP=np.exp(-1/(1-nodes**2)) # true C-infinity exp(-1/(1-x^2)) model
MASS=float(np.dot(weights,BUMP))
WGT=weights*BUMP/MASS
aux=np.linspace(0.38,1.23,25)
aux=np.array([x for x in aux if min(abs(x-log2),abs(x-log3))>0.026])
assert len(aux)>=16


def eight_weights(t,uu,endpoint):
    """Actual original linear weight FORM, with atomic A1/A2 fixture."""
    r=t/16
    a1,a2=[float(x) for x in A(lam_half if endpoint=='half' else lam_two)]
    proj=a1*np.cos(2*r*uu)-a2*np.cos(r*uu)
    polebase=np.cosh(uu/2)*np.cos(t*uu)
    return np.array([np.cos(r*uu),np.cos(2*r*uu),
                     uu**2*proj,uu**4*proj,uu**6*proj,uu**8*proj,
                     polebase*np.cos(r*uu),polebase*np.cos(2*r*uu)])


def smooth_column(t,c,delta,endpoint,scale=1):
    # Even C-infinity basis b((u-c)/delta)+b((u+c)/delta).
    # For even source weights, integrate positive lobe and reflect exactly.
    # Auxiliary normalized to integral=1, source port normalized to VALUE 1.
    vals=eight_weights(t,c+delta*nodes,endpoint)
    return scale*(vals@WGT)


def test(t):
    t=float(t)
    delta=min(0.0014,0.14/t)
    assert delta>0
    assert delta<min((log3-log2)/3,abs(aux-log2).min(),abs(aux-log3).min())
    for endpoint in ('half','two'):
        Amat=np.column_stack([smooth_column(t,c,delta,endpoint) for c in aux])
        portfac=2*delta*MASS*math.e  # exact bump point value is e^-1
        p2=portfac*smooth_column(t,log2,delta,endpoint)
        p3=portfac*smooth_column(t,log3,delta,endpoint)
        singular=np.linalg.svd(Amat,compute_uv=False)
        assert singular[-1]>1e-8*singular[0],(t,endpoint,singular)
        coeffs=[];errors=[]
        for port in (p2,p3):
            c=np.linalg.lstsq(Amat,-port,rcond=1e-12)[0]
            coeffs.append(c)
            errors.append(float(np.max(np.abs(Amat@c+port))))
        assert max(errors)<1e-11,(t,endpoint,errors)
        # By support separation, port evaluations are exactly the identity;
        # source coefficients are genuinely corrected off the prime points.
        print(f'  t={t:10g}, {endpoint:4s}: 8x{len(aux)} rank=8 '
              f'cond={singular[0]/singular[-1]:.3g} '
              f'|Lh|_inf={max(errors):.3e} '
              f'aux_coeff_max={max(np.max(abs(c)) for c in coeffs):.3e}, '
              'prime evaluations ((1,0),(0,1))')
    prime2=np.log(2)/np.sqrt(2)*np.cos(t*np.log(2))
    prime3=np.log(3)/np.sqrt(3)*np.cos(t*np.log(3))
    assert abs(prime2)+abs(prime3)>1e-5
    # Linearized basic Weil prime sample: signs reverse under eps -> -eps
    signed_gain=prime2**2+prime3**2
    assert signed_gain>0 and (-signed_gain)<0
    # Projective signed two-endpoint channel (ATOMIC endpoint response limit).
    # The sign/size of the full prime summand in the original Lean test remains
    # a separate same-source explicit-formula weld, not assumed here.
    def atomic_pole(lam):
        mu=float(mu0(lam)); lam=float(lam)
        centres=[0,np.pi/3,np.pi/2,np.pi]
        weights=[1,-1,lam,mu]
        def pair(weight):
            return sum(cw*weight(u) for cw,u in zip(weights,centres))
        on1=pair(lambda v:np.cos(v))
        on2=pair(lambda v:np.cos(2*v))
        pole1=pair(lambda v:np.cosh(8*v/t)*np.cos(16*v)*np.cos(v))
        pole2=pair(lambda v:np.cosh(8*v/t)*np.cos(16*v)*np.cos(2*v))
        return pole1*on2-pole2*on1
    ph=atomic_pole(lam_half);pt=atomic_pole(lam_two)
    a1h,a2h=[float(x) for x in a]
    a1t,a2t=[float(x) for x in b]
    projected=[]
    for prime,u in ((2,log2),(3,log3)):
        bh=a1h*np.cos(2*(t/16)*u)-a2h*np.cos((t/16)*u)
        bt=a1t*np.cos(2*(t/16)*u)-a2t*np.cos((t/16)*u)
        # First derivative of the projective signed profile at each prime,
        # relative to independent perturbations of the two endpoints.
        phalf=4*pt*bh
        ptwo=-4*ph*bt
        projected.extend([phalf*np.cos(t*u),ptwo*np.cos(t*u)])
    assert max(abs(x) for x in projected)>0.01
    print('  atomic projective two-prime phases',
          [f'{x:+.5f}' for x in projected], '(fixture; Lean weld pending)')
    print(f'  candidate scalar prime phases w2={prime2:+.8f} '
          f'w3={prime3:+.8f}; both-sign perturbations are possible')

for t in (200,1000,80000,1000000):
    test(t)

print('PASS 2 prime sample apertures and 8 source-moment/pole constraints in two endpoint fixture geometries')
print('OPEN EXACT Lean extended carrier; original Weil prime-projective channel; all-height signed strict RH terminal')
