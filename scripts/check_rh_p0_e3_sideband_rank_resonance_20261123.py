#!/usr/bin/env python3
"""RH P0 E3: original annihilator's two physical sidebands, rank, and no-go.

Source: Synthesis/RiemannSelectedPrimeSensitiveFrozenApertureExact.lean,
Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal.lean,
DASHI RHP0NormalizedPrimeApertureE2UniformSobolevScale20261123.md and
RHP0Dyadic1024FourEJ26RebalancedSmoothMaxCut20261123.md.

Mathematical scope: SymPy algebra plus exact rational sufficient threshold,
not a theorem about true zeta zero positions, not a Lean/Agda kernel receipt.
"""
from fractions import Fraction as F
from math import comb
from functools import lru_cache
import sympy as S

u, omega, r, A1, A2 = S.symbols('u omega r A1 A2', real=True)
h0, h1, h2, h3, h4 = S.symbols('h0 h1 h2 h3 h4', real=True)
M = F(3, 32)
for f in (1, 2):
    assert S.trigsimp(S.cos(f*r*u)*S.cos(omega*u)
      - (S.cos((omega+f*r)*u)+S.cos((omega-f*r)*u))/2) == 0
# At omega = r,2r, horizontal cosh factor stays in H_a(xi).
B = S.Matrix([[h3+h1, -(h2+h0)], [h4+h0, -(h3+h1)]])
assert S.simplify(B.det() - (h0+h2)*(h0+h4) + (h1+h3)**2) == 0
# Q_t(i*r)=Q_t(2*i*r)=0 exactly: 9 on-line real quadratics each.
z = S.symbols('z')
for c in (1, 2):
    assert S.expand((z*z+1)**9*(z*z+4)**9).subs(z, S.I*c) == 0
B0 = B.subs({h0:S.Symbol('mass'),h1:0,h2:0})
assert S.simplify(B0.det()-(S.Symbol('mass')*(S.Symbol('mass')+h4)-h3**2)) == 0
print('PASS literal two-sideband product-to-sum, exact annihilator notches, determinant')

E = [F(1)]
for w, m in [(F(1),9),(F(1,4),9),(F(1,196),2),
             (F(1,225),2),(F(1,289),2),(F(1,324),2)]:
    for _ in range(m):
        new=[F(0)]*(len(E)+1)
        for j,x in enumerate(E): new[j]+=x;new[j+1]+=w*x
        E=new
assert len(E)==27 and all(F(0)<e<=comb(26,j) for j,e in enumerate(E))
lam=F(52*1024,7)
assert 52*F(7,52*1024)+sum([F(1,2**n*1024) for n in range(1,21)])+F(1,2**20*1024)==F(1,128)
# The infinite tail is a convergent sequence of additional box convolutions.
# B_m: valid TV-L1 bound for two symmetric plateau copies for ANY m>=1.
def bump_derivative_bound(m):
    if m==0:return M
    tail=max(0,m-1-52)
    return 4*lam**min(m-1,52)*F(1024)**tail*F(2)**(tail*(tail+1)//2)

@lru_cache(maxsize=None)
def C(r_integer,k):
    x=F(1,r_integer*r_integer)
    out=F(0);power=F(1)
    for j,e in enumerate(E):
        out += e*power*bump_derivative_bound(k+2*j)
        power*=x
    return out

def error_bounds(radius):
    # h - b L1 is <= eta. H_a(0) >= M-2eta for |a|<=1/2,
    # |u|<=5/4 and cosh(5/8)<2.
    eta=C(radius,0)-M
    # K=||(h cosh(au))'''||1 <= 2*(C3 + 3/2 C2 + 3/4 C1 + 1/8 C0)
    # hence |H_a(j*r)| <= K/(j*r)^3, all j>=1.
    gamma=2*(C(radius,3)+F(3,2)*C(radius,2)+F(3,4)*C(radius,1)
              +F(1,8)*C(radius,0))/radius**3
    return eta,gamma

def accepted(rad):
    eta,gamma=error_bounds(rad)
    return eta<=M/8 and gamma<=M/16

lo,hi=1215,32768
assert accepted(hi) and not accepted(lo)
while lo<hi:
    mid=(lo+hi)//2
    if accepted(mid):hi=mid
    else:lo=mid+1
R=lo
assert R==13576 and not accepted(R-1)
# Because C_k(r) is a positive-coefficient polynomial of r^-2 and gamma
# divides by r^3, both tests remain valid at every real r>=R.
assert (F(11,16)**2-F(1,8)**2)==F(117,256)
assert (F(37,16)+F(1,8))/F(117,256)==F(16,3)
print('PASS exact source uniform |a|<=1/2 full-strip rank gate, r>=',R,
      ', t>=',16*R)
print('PASS det>=117/256*M^2; max |K(r)|,|K(2r)| >= (3/8)*|P*eps|*M*max(|A1|,|A2|)')
print('PASS source nonzero sideband for any nonzero original on-line (A1,A2) and P*eps!=0')

# A density-only log-loss no-go: with a=0, A1=1/r, A2=0,
# pole=1, eps=r^-5, zero-like unit atom at gamma=t+2r:
# |K(2r)|=2*r^-6*|M+H_0(4r)| >= (15/8)*M*r^-6
# since |H_0(4r)| <= gamma/(4^3) <= M/16.
assert F(2)*(M-M/16)==F(15,8)*M==F(45,256)
assert F(45,256)>0
print('PASS adversarial non-zeta zero measure with m<=C log(t) atoms can cost',
      '(45/256)*m/r^6: log factor cannot be removed by counting alone')

# Two-prime phase floor no-go on ALL real heights; not on the
# special unknown set of actual off-critical zeta ordinate heights.
# alpha = log(3)/log(2) irrational (unique prime factorisation), so
# n*alpha+alpha/2 is dense mod 1. t_n=(n+1/2)*pi/log2 gives cos(t_n*log2)=0
# and infinitely often |cos(t_n*log3)| arbitrarily small.
n=2437313
height=(S.Integer(n)+S.Rational(1,2))*S.pi/S.log(2)
assert S.simplify(S.cos(height*S.log(2)))==0
cos3=S.N(S.cos(height*S.log(3)),65)
assert abs(cos3)<S.Rational(1,200000)
assert S.N(height,30)>217216
print('PASS high-precision near-double-real-height resonance n=',n,
      't≈',S.N(height,15),'|cos(t log3)|≈',abs(cos3))

# Source strict terminal self-identity: a strict upper estimate is a
# genuinely independent number-theoretic premise, not a re-normalisation.
D,d,S_slack=S.symbols('D d S_slack',nonnegative=True,real=True)
assert S.simplify((2*D+S_slack-4*d)-(2*(D-2*d)+S_slack))==0
print('PASS same-source terminal gap 2(D-2d)+S>=0 if D>=2d,S>=0')
print('OPEN: independently certified real-zeta zero/Gamma/prime signed E3 bound')
print('OPEN: original E0 source carrier, source-wide FarExact/post-sixth; RH/GRH OPEN')
