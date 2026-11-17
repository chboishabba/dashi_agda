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
# GELU exact GLOBAL first-derivative bound. g''(t)=
# (2-t²)*phi(t), so stationary points of g' are ±sqrt(2);
# g'(-sqrt2)=1-g'(sqrt2)<0 and limits are 0 and 1.
# Consequently |g'|<=L*=Phi(sqrt2)+sqrt2 phi(sqrt2).
# This tightens the loose 1+1/sqrt(2*pi*e) bound in the R4
# recurrence without assuming any fitted network weight norms.
derivative=S.diff(g(t),t)
root=S.sqrt(2)
Lstar=S.simplify(derivative.subs(t,root))
Lformula=(1+S.erf(1))/2+S.exp(-1)/S.sqrt(S.pi)
check("exact GELU optimum first derivative expression",
      S.simplify(Lstar-Lformula)==0)
check("GELU negative stationary derivative is 1 minus maximum",
      S.simplify(derivative.subs(t,-root)-(1-Lstar))==0)
check("GELU first derivative reaches stationary extrema",
      S.simplify(dd.subs(t,root))==0
      and S.simplify(dd.subs(t,-root))==0)
check("exact source GELU global Lipschitz sharpens loose bound",
      float(Lstar)<float(1+1/S.sqrt(2*S.pi*S.E))
      and float(Lstar)>1)
# The EVEN nonlinear channel has global Lipschitz
# L_even=Lstar-1/2 (bias-free GELU even projection).
even_derivative=S.diff(even_g(t),t)
check("GELU even derivative equals total derivative minus half",
      S.simplify(even_derivative-derivative+S.Rational(1,2))==0)
check("even-channel sharp derivative maximum at sqrt2",
      S.simplify(even_derivative.subs(t,root)
        -(Lstar-S.Rational(1,2)))==0)
# Curvature gives a global quadratic envelope for the even
# projection around preactivation bias b:
# |(g(b+t)+g(b-t))/2-g(b)| <= t²/sqrt(2*pi).
# Source second-derivative extremum is sqrt(2/pi).
# At b1=0 the bias-free E_g is O(t²), not generically O(t).
# This enables a chart-flip alternative to strict orientation
# stability when downstream tolerates a bounded residual.
for z1 in [R(0),R(1,4),R(1,2),R(1),R(2),R(4)]:
    for bias_value in [R(-2),R(0),R(1)]:
        curvature=S.N((g(bias_value+z1)+g(bias_value-z1))/2
                  -g(bias_value),40)
        envelope=S.N(z1*z1/S.sqrt(2*S.pi),40)
        check("centered GELU even curvature bound "+str((z1,bias_value)),
              abs(curvature)<=envelope)
# Source FFN output with W1-bias b, W2-scale m and output bias b2
# obeys |even_F(z)| <= |F(0)|
#   + |m| min((Lstar-1/2)|k*z|, |k*z|²/sqrt(2*pi)).
# For same state and arbitrary sign-chart flip:
# |y_plus-y_minus|=2|even_F(z)|. Original affine transition
# gives |h_pre_plus-h_pre_minus|=2|Ty*even_F(z)+bT|.
# The source history cap is nonexpansive in the exact Euclidean model.
for zz in [R(-2),R(-1,2),R(0),R(1,2),R(2)]:
    zvalue=S.N(zz,50);bvalue=S.N(R(1,3),50)
    projection=S.N((F(zz)+F(-zz))/2,45)
    centre=S.N(F(0),45)
    dt=abs(k*zz)
    # instantiate k=2,m=3,b2=-1/4 for a nontrivial biased FFN
    sub={k:2,m:3,b:R(1,3),b2:R(-1,4)}
    proj=S.N(projection.subs(sub),40)
    ctr=S.N(centre.subs(sub),40)
    normz=abs(2*zz)
    bound=3*min(float((Lstar-S.Rational(1,2))*normz),
                float(S.N(normz**2/S.sqrt(2*S.pi),40)))
    check("source biased even chart residual bound "+str(zz),
          abs(float(proj-ctr))<=bound+1e-12)

# Original hard sign has THIRD case sigma=0 at unique fixed point
# z=(x,h)=0 in non-raw route. Source y=sign*y_c and
# updated_h=cap_history(sign*h_c) then both vanish even when
# learned FFN and transition contain nonzero biases. This is NOT
# captured by the two-chart identity sigma in {-1,+1}.
def oriented_output(sign,preact):
    return sign*F(sign*preact)
check("original sign-zero fixed point gives zero output",
      S.simplify(oriented_output(S.Integer(0),S.Integer(0)))==0)
check("nonzero output bias prevents center-to-chart continuity",
      S.simplify(oriented_output(S.Integer(1),S.Integer(0))
              -oriented_output(S.Integer(0),S.Integer(0))
              -(m*g(b)+b2))==0)
# More generally for different z,z' and signs sigma,sigma',
# add and subtract the intermediate same-sign y_sigma(z'):
# |delta y| <= L_F |delta z| + [sigma!=sigma'] 2|E_F(z')|,
# where L_F=|m*k| Lstar for scalar learned two-linear FFN.
# This gives an APPROXIMATE branch-agnostic consumer budget,
# not equality of returned orientation sign metadata.
for src,qp in [(R(1,50),R(1,48)),(R(-1,2),R(-2,5)),
               (R(2),R(9,5))]:
    sub={k:2,m:3,b:R(1,3),b2:R(-1,4)}
    yu=S.N(oriented_output(S.Integer(1),src).subs(sub),45)
    yv=S.N(oriented_output(S.Integer(-1),qp).subs(sub),45)
    even_here=S.N(even.subs(t,qp).subs(sub),45)
    Lf=S.N(6*Lstar,45)
    chart_bound=Lf*abs(src-qp)+2*abs(even_here)
    check("source cross-chart input-perturbation bound "+
          str((src,qp)),abs(yu-yv)<=chart_bound)
# Bias-free GELU has quadratic chart jump near the zero preactivation,
# but with learned biases a constant chart residual may remain.
eps=R(1,100)
check("bias-free tiny GELU sign jump has quadratic upper bound",
      float(abs(g(eps)+g(-eps)))
      <=float(2*eps**2/S.sqrt(2*S.pi)))
check("bias alone can cause order-one chart residual",
      S.simplify((Fp+Fm).subs({m:0,b2:1})-2)==0)

print("X369_GELU_PARITY_HISTORY_SYMPY_PASS",len(checks),"checks")
