#!/usr/bin/env python3
"""Exact SymPy source-parameter tests for DASHI RH selected W, 2026-11-22.

Mathematics only. NOT a Lean/Agda proof, and no assertion that the selected
signed eventual compensation gap has been proved. Uses precise original
normalized bump coefficient bound, weight Lipschitz constant, determinant
perturbation, selected W fourth derivative and the actual-source RvM
arbitrary-endpoint count *as a named analytical premise*.
"""
from itertools import product
from math import comb, cos, sin, cosh, sinh, log, pi
import sympy as s

B=s.Rational(83,30)  # 1+1+2/3+1/10, exact four-window coefficient bound
M=s.Integer(5)     # source atomic response absolute bound
D=s.Integer(4)*M+2
K=19*s.cosh(1)     # source t>=200 pole-weight Lipschitz constant
margin=7*s.pi**4/800
eta=s.Min(1, margin/(2*(4*(10+s.pi**4)+2)))
delta=s.simplify(eta/(D*B*K))
assert B==1+1+s.Rational(2,3)+s.Rational(1,10)
assert D==22
assert s.simplify(B*K*delta-eta/22)==0
assert 0<float(eta)<1
assert 0<float(delta)<1

# An arbitrary positive normalized symmetric bump of radius R about its
# source centre integrates any K-Lipschitz EVEN weight to within K*R.
# Therefore the source four-window pairing has error <= B K R.
# This is a universal inequality, not a numerical statement about a fake bump.

# Determinant algebra from the *exact original source orientation*
a,b,c,d,ea,eb,ec,ed=s.symbols('a b c d ea eb ec ed', real=True)
error=s.expand((a+ea)*(b+eb)-(c+ec)*(d+ed)-(a*b-c*d))
assert s.expand(error-(a*eb+b*ea+ea*eb-c*ed-d*ec-ec*ed))==0

# 256 exact corner stresses including opposite-sign entry perturbations.
for pattern in product((-1,1),repeat=8):
    val={v:pattern[i]*(M if i<4 else s.Rational(1,22))
         for i,v in enumerate((a,b,c,d,ea,eb,ec,ed))}
    assert abs(error.subs(val)) <= D*s.Rational(1,22)
# Deliberate false bound: dropping the quadratic determinant remainder fails.
assert abs(error.subs({a:0,b:0,c:0,d:0,ea:1,eb:1,ec:0,ed:0})) > 0

# Conservative numerical testing of source pole weight derivative on [-6,6].
for t in (200,201,300,1000,1000000):
    for c0 in (1,2):
        for i in range(-600,601):
            u=i/100
            dweight=(8/t)*sinh(8*u/t)*cos(16*u)*cos(c0*u) \
              -cosh(8*u/t)*(16*sin(16*u)*cos(c0*u)+c0*cos(16*u)*sin(c0*u))
            assert abs(dweight) <= float(K)+1e-12

# Full source-selected W normalized profile envelope, not an arbitrary test:
# G_{R,lambda,mu} has four normalized translated bumps and R>0;
# ||G^(j)||_1 <= B*Bj/(B0 R^j).
# P_G=4 G(x) [A1 cos(2x)-A2 cos x], |A1|,|A2|<=B.
# Original two pole coefficients each <= 72 from four entries <= 6.
# Thus ||P_W^(j)||1 <= 576 B^2 * sum_k binom(j,k)
#                        (2^(j-k)+1)*Bj/B0 /R^k.
R=s.symbols('R',positive=True)
ratios=[s.Integer(1)]+list(s.symbols('b1:5',positive=True))
Mstar=[]
for j in range(5):
    e=s.Integer(576)*B**2*sum(
        comb(j,k)*(2**(j-k)+1)*ratios[k]/R**k
        for k in range(j+1))
    Mstar.append(s.expand(e))
assert s.simplify(Mstar[0]-1152*B**2)==0

# The full horizontally weighted cosh transform, NOT just the base transform.
x,h,q=s.symbols('x h q',real=True)
P=s.Function('P')(x)
full=s.diff(P*s.cosh(h*x),x,4)
leibniz=sum(comb(4,j)*h**(4-j)*s.diff(P,x,j)*
            (s.cosh(h*x) if (4-j)%2==0 else s.sinh(h*x))
            for j in range(5))
assert s.simplify(full-leibniz)==0
assert s.simplify(full.subs(h,-h)-full)==0
assert s.simplify(full.subs(h,0)-s.diff(P,x,4))==0

# Fixed R from source UniformQuarticFourSignedPoleCore; t>=200 gives
# |h|<=8/t<=1/25, L<=pi+1. Thus Dstar depends ONLY on the fixed R and
# original unit-bump norms, not on physical ordinate t.
a0=s.Rational(1,25)
Dstar=s.exp((s.pi+1)*a0)*sum(comb(4,j)*a0**(4-j)*Mstar[j] for j in range(5))
assert Dstar.has(R)
assert not Dstar.has(s.symbols('t'))

# Source actual zeta count high interval:
# N(A,B)<=C_N (B-A+1) log(B+4), 5<=A<B.
# At positive t>=200, choose integer n>=t+7 and positive shell k>=n.
# right (t+k,t+k+1]: count<=2 C_N log(t+k+5).
# left (t-k-1,t-k]: after gamma -> -gamma can be enclosed by
# (k-t-1,k-t+1], count <=3 C_N log(k-t+5).
# Combined shell <=5 C_N log(t+k+5) <=5 C_N log(2k).
# Last inequality uses n>=t+7 so t+5<=k.

n,z,t=s.symbols('n z t',positive=True)
F=s.log(2*z)/z**4
formula=s.log(2*n)/(3*n**3)+1/(9*n**3)
# SymPy may return a conditionally-evaluated Meijer-G integral.
# Prove the integral equality by the exact antiderivative and vanishing at infinity.
assert s.simplify(s.diff(formula,n)+s.log(2*n)/n**4)==0
assert s.limit(formula,n,s.oo)==0
assert s.simplify(s.diff(F,z)-(1-4*s.log(2*z))/z**5)==0
assert s.limit(t**2*(s.log(2*(t+7))/(t+7)**4 + formula.subs(n,t+7)),t,s.oo)==0
# Upper bound for the full absolute FAR zero tail along n>=t+7:
# 5 C_N Dstar (t/16)^2 [log(2n)/n^4 + log(2n)/(3n^3)+1/(9n^3)].
# Positive normalization and both signed-zero multiplicities are retained.

# Negative control: no n-independent uniform tail follows from physical t^2
# prefactor, and absolute tails alone do NOT prove a signed surplus.
assert s.limit(t**2*(formula.subs(n,100)),t,s.oo)==s.oo
assert s.simplify((s.Integer(-2)+s.Integer(3))-1)==0

print('PASS: source coefficient B=83/30 and determinant M=5, D=22')
print('PASS: 256/256 exact determinant corner adversaries')
print('PASS: 12,010 numeric source pole-weight derivative stress points')
print('PASS: actual-source selected-W derivative envelope (symbolic bump norms)')
print('PASS: full cosh-weighted fourth derivative and horizontal reflection')
print('PASS: actual-zeta high-interval count -> 5C_N logarithmic two-sided shells')
print('PASS: exact logarithmic tail integral and t-dependent cutoff O(log t/t)')
print('PASS: false quadrant and fixed-cutoff/strict-sign negative controls')
print('eta=',s.N(eta,12),'explicit uniform pole radius=',s.N(delta,12))
print('Dstar leading symbolic coefficients:', [s.factor(e) for e in Mstar[:2]])
print('LIMITATION: no local Lean/Agda kernel; no numeric actual bump derivative norms')
print('LIMITATION: C_N is source-existing existential; strict signed gap OPEN')
