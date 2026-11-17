#!/usr/bin/env python3
"""Leech R4 GELU parity and signed history-transition exact/source weld.

Reuses repo-owned LeechGELUParityHistoricalSafetySteelman20261031.md,
LeechOddOnlyApproximationObstructionExact.agda,
LeechSignedHistoryExpertBidiExact.agda and LeechLayerErrorTransportExact.agda.

Original LeechTransformer HistoryOrbitMoE.step selected expert:
 canon_z = sigma*(x,h);
 F(canon_z) = W2 GELU(W1 canon_z + b1) + b2;
 y_sigma=sigma*F(sigma*z);
 h_pre_sigma=sigma*T(sigma*h,sigma*x,F(sigma*z)),
 T=Th*h+Tx*x+Ty*y_c+bT;
 h_next=cap_history(h_pre_sigma).

All algebra is real exact; source floating GELU/softmax, sign fallback,
training straight-through gradients and learned parameters need receipts.
"""
import sympy as S
R=S.Rational
checks=[]
def check(label,condition):
    if not bool(condition):raise AssertionError("X369_GELU_PARITY_FAIL "+label)
    checks.append(label)
t,k,b,m,b2=S.symbols("t k b m b2",real=True)
g=lambda z:z*(1+S.erf(z/S.sqrt(2)))/2
even_g=lambda z:z*S.erf(z/S.sqrt(2))/2
F=lambda z:m*g(k*z+b)+b2
Fp,Fm=F(t),F(-t)
odd=(Fp-Fm)/2
even=(Fp+Fm)/2
check("source exact GELU reflection",
      S.simplify(g(-t)-g(t)+t)==0)
check("source original GELU odd = half identity",
      S.simplify((g(t)-g(-t))/2-t/2)==0)
check("source original GELU even = erf nonlinear",
      S.simplify((g(t)+g(-t))/2-even_g(t))==0)
check("learned biased FFN parity reconstruction",
      S.simplify(Fp-(odd+even))==0)
check("source + chart equals odd plus even",
      S.simplify(Fp-(odd+even))==0)
check("source - chart equals odd minus even",
      S.simplify(-Fm-(odd-even))==0)
check("source chart difference exactly twice even",
      S.simplify(Fp+Fm-2*even)==0)
check("zero first-layer bias odd channel linear",
      S.simplify(odd.subs(b,0)-m*k*t/2)==0)
check("zero first-layer bias even channel nonlinear plus b2",
      S.simplify(even.subs(b,0)-m*even_g(k*t)-b2)==0)
# Original selected expert FFN sign flip at same input/history:
# output changes only by the even part, including learned biases.
check("source chart flip bias at zero input",
      S.simplify(2*even.subs(t,0)-2*(m*g(b)+b2))==0)
# Distinguish sign flip from earlier SAME-sign history collision.
check("source signed-history input collision differs by full GELU odd part",
      S.simplify(g(1)-g(-1)-1)==0)
check("pure GELU chart flip at z=1 equals erf factor",
      S.simplify(g(1)+g(-1)-S.erf(1/S.sqrt(2)))==0)
# GELU curvature gives a quadratic bound around the learned bias.
phi=lambda z:S.exp(-z**2/2)/S.sqrt(2*S.pi)
dd=S.simplify(S.diff(g(t),t,2))
check("GELU second derivative exact",
      S.simplify(dd-(2-t**2)*phi(t))==0)
check("global curvature extremum at zero and at |t|=2",
      S.simplify(dd.subs(t,0)-2/S.sqrt(2*S.pi))==0
      and S.simplify(S.diff((t*t-2)*S.exp(-t*t/2),t)
          .subs(t,2))==0)
# Global real inequality: |g''(t)|<=sqrt(2/pi).
# Proof: on 0<=t²<=2, (2-t²)e^-t²/2<=2.
# on t²>=2, (t²-2)e^-t²/2 peaks at t²=4,
# with value 2 e^-2 < 2.
for zz in [R(-5),R(-2),R(-1),R(0),R(1),R(2),R(5)]:
    check("curvature sampled domination "+str(zz),
          float(abs(dd.subs(t,zz)))<=float(S.sqrt(2/S.pi)))
# Exact parity MSE obstacle: no odd-only approximation can match
# a biased learned FFN on both mirrored historical inputs unless
# its even component vanishes.
student=S.symbols("student",real=True)
pair_MSE=((Fp-student)**2+(Fm+student)**2)/2
check("pairwise odd-student MSE floor exact identity",
      S.simplify(pair_MSE-even**2-(odd-student)**2)==0)
# Original transition and orientation chart restoration:
# T operates on (sigma*h, sigma*x, F(sigma*z)) and is affine.
th,tx,ty,bt,h,x=S.symbols("Th Tx Ty bT h x",real=True)
def raw_history(sign):
    return sign*(th*(sign*h)+tx*(sign*x)+ty*F(sign*t)+bt)
Hplus=raw_history(S.Integer(1))
Hminus=raw_history(S.Integer(-1))
check("source oriented transition factors via external FFN output",
      S.simplify(Hplus-(th*h+tx*x+ty*Fp+bt))==0
      and S.simplify(Hminus-(th*h+tx*x-ty*Fm-bt))==0)
check("source history chart difference even and transition bias",
      S.simplify(Hplus-Hminus-2*(ty*even+bt))==0)
check("history chart invariant if even FFN and transition bias vanish",
      S.simplify((Hplus-Hminus).subs({m:0,b2:0,bt:0}))==0)
# Source radial history_cap is Euclidean projection onto a ball.
# It is 1-Lipschitz in exact Euclidean geometry and thus bounds
# the post-cap chart discrepancy by pre-cap difference; actual
# torch float64 norm / dtype cast requires separate numeric slack.
# This finite scalar cap witness does not claim a tensor proof.
def clamp(z,cap): return min(max(z,-cap),cap)
for p,qv in [(R(3),R(-2)),(R(1,2),R(4)),(R(-5),R(-7))]:
    check("scalar cap is nonexpansive "+str((p,qv)),
          abs(clamp(p,R(2))-clamp(qv,R(2)))<=abs(p-qv))
# For a fixed selected expert, chart change is NOT automatically a
# discontinuity of the whole output of magnitude 2||F||:
# it is exactly 2||even(F)||. With b1=0, b2=0,
# |even_g(a)| <= min(|a|/2, a²/sqrt(2pi)).
# The latter is useful near zero; source trained W norms still OPEN.
check("even GELU quadratic leading term",
      S.simplify(S.limit(even_g(t)/t**2,t,0)
                 -1/S.sqrt(2*S.pi))==0)
check("even GELU has nonzero fourth-order correction",
      S.simplify(S.diff(even_g(t),t,4).subs(t,0))!=0)
print("X369_GELU_PARITY_HISTORY_SYMPY_PASS",len(checks),"checks")
