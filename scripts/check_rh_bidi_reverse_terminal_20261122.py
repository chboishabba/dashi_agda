#!/usr/bin/env python3
"""Exact 2026-11-22 DASHI RH R2/G3/Agda bidirectional terminal audit.

Original source bodies examined:
 Lean: RiemannProjectiveQuarticFourWindowSignedPoleConeDecomposition,
       RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal,
       RiemannProjectiveQuarticFourWindowSignedPoleFourierMass,
       RiemannProjectiveQuarticFourWindowAtomic[Corridor/PoleSign].
 Agda: RiemannG2ClayTerminalBishopLocatedExact,
       RiemannG2UniformCertifiedHighOffLineProducerExact,
       RiemannG2ZeroSideHMBypassBidiExact,
       RiemannG2HASingleSourceProducerBidiExact.

Only exact scalar algebra and finite geometry. Neither script source-readback nor
SymPy can admit an RH/GRH theorem, prove a zero-weighted inequality, or typecheck.
"""
from fractions import Fraction
from itertools import product
import sympy as s

# ORIGINAL EXACT POST-SIXTH TERMINAL, NOT ONLY THE OLD G3 COMPILER:
# W.completedSignedResidual = 1/2*(H - I)
# W.canonicalLocalBudgetSlack = S >= 0
# PostSixthCanonicalSignedHighCut iff C + S/2 < 2*d.
# Therefore exact and terminal-strength analytic leaf is H + S < 4*d+I.
H,I,d,S=s.symbols('H I d S',real=True)
C=(H-I)/2
T=4*d+I
assert s.simplify(2*(C+S/2-2*d)-(H+S-T))==0
assert s.simplify(2*(C-2*d)-(H-T))==0
terminal_checks=0
for h,i,dd,ss in product((s.Rational(-1),s.Rational(0),s.Rational(3),s.Rational(5)),
                         (s.Rational(-2),s.Rational(0),s.Rational(2)),
                         (s.Rational(1,2),s.Rational(1),s.Rational(2)),
                         (s.Rational(0),s.Rational(1),s.Rational(3))):
    L={H:h,I:i,d:dd,S:ss}
    assert bool((C+S/2<2*d).subs(L))==bool((H+S<T).subs(L))
    terminal_checks+=1
# FALSE converse: G3 completed residual strict without local slack is insufficient.
neg={H:3,I:0,d:1,S:2}
assert (C<2*d).subs(neg) == s.true
assert (C+S/2<2*d).subs(neg)==s.false

# ORIGINAL SAME-SOURCE CONE/GOOD/FAR finite decomposition.
# In cone, exact scalar x = max(x,0)-max(-x,0).
# In good, quartic p<=0 and exact x=p+r; good gain=-p,
# good remainder upper is |r|. Far lane retains exact sign.
for x in (s.Rational(-5,2),s.Rational(-1),s.Integer(0),s.Rational(2,3)):
    assert x==max(x,0)-max(-x,0)
    for rr in (s.Rational(0),s.Rational(3,2)):
        old_cone=max(x,0)+rr
        sharp_cone=max(x,0)-max(-x,0)
        assert sharp_cone<=old_cone
for p in (s.Rational(-3),s.Rational(-1),s.Rational(0)):
    for r in (s.Rational(-2),s.Rational(0),s.Rational(5,2)):
        assert p+r <= p+abs(r)
# Old unsharpened gap NOT equivalent to sharpened gap:
# cone exact=-3, no remainder, far=good=0, target=-1.
assert (-3 < -1) and not (0 < -1)

# Even exact sharpened finite budget still overestimates a good-region source
# if r is negative and its absolute value is charged as a positive debt.
p=s.Integer(-2); r=s.Integer(-3)
assert p+r==-5 and p+abs(r)==1

# CRITICAL-LINE GEOMETRY: signed first order cancels, even defect doubles;
# quartic selected G3 phase is sign-indefinite on each half side.
a,q=s.symbols('a q',real=True)
Q=a*a*q*q-(a**4+q**4)/6
assert s.simplify(Q.subs(a,-a)-Q)==0
assert s.simplify(Q.subs(q,-q)-Q)==0
assert s.simplify(Q.subs(q,0)+a**4/6)==0
assert s.simplify(Q.subs(q,a)-s.Rational(2,3)*a**4)==0

# Recover ORIGINAL selected W atomic geometry with zero J2;
# NOT a claim about smoothed W or actual nontrivial zeros.
lam=s.symbols('lam',real=True)
mu=(13*lam-8)/(144-54*lam)
J2= -s.pi**2*(54*lam*mu+13*lam-144*mu-8)/72
assert s.cancel(J2)==0
J4=-s.pi**4*(2430*lam*mu+97*lam-5184*mu-32)/2592
for v in (s.Rational(1,2),s.Rational(2,3)):
    assert s.N(J4.subs(lam,v))<0
assert mu.subs(lam,s.Rational(1,2)) == -s.Rational(1,78)
assert mu.subs(lam,s.Rational(2,3)) == s.Rational(1,162)
centers=(s.Integer(0),s.pi/3,s.pi/2,s.pi)
def profile(L,qval):
    m=mu.subs(lam,L)
    A1=s.Rational(1,2)-m
    A2=s.Rational(3,2)-L+m
    return 4*sum(w*(A1*s.cos(2*x)-A2*s.cos(x))*s.cos(qval*x)
                 for w,x in zip((1,-1,L,m),centers))
def limit_selected(qval):
    first=s.Rational(1,2); second=s.Rational(2,3)
    pole=lambda x:3*(2-x)/4
    return s.simplify(pole(second)*profile(first,qval)-pole(first)*profile(second,qval))
assert limit_selected(0)==0
assert limit_selected(1)==-s.Rational(80,351)
assert limit_selected(2)==-s.Rational(320,351)
assert limit_selected(4)==0
# Negative far source is genuinely part of original selected atomic geometry.
# Replacing farExact with |farExact| loses this negative compensation.
assert limit_selected(2)<0

# Local versus global quantifiers cannot be swapped:
# For each pair (t,rho), there is an eps>0, but the infimum over an
# unbounded family of positive eps can be zero (eps_n=1/(n+1)).
n=s.symbols('n',integer=True,nonnegative=True)
eps=1/(n+1)
assert s.limit(eps,n,s.oo)==0
assert s.simplify(eps.subs(n,0)-1)==0

print(f'PASS {terminal_checks}/{terminal_checks} terminal-strength scalar equivalence tests')
print('PASS G3-only cut is insufficient when local slack >0 (counterexample)')
print('PASS sharpened cone/good/far exact budgets and converse failures')
print('PASS four selected atomic moments / q-sign geometry and quartic two-sided parity')
print('PASS source level variable margin does not give uniform global epsilon')
print('LITERAL NEW MINIMAL LEAF: H_W+S_W < 4*d_W(rho)+I_W')
print('UNPAID: any same-zero signed margin, Agda analytic carrier weld, native Lean/Agda kernel, external original axioms')
