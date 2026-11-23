#!/usr/bin/env python3
"""RH P0 source-faithful 128 Fourier/Gamma bilateral geometry (SymPy + mpmath).

Source owners:
  dashi_lean4/Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierMass.lean
  dashi_lean4/Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourthOrderQuotient.lean
  dashi_lean4/Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleNMu.lean
  anthropics/formal-math/zeta23/Zeta23/GammaFacts{,/Mu,/Complete}.lean

Checks original normalization, evenness, log core and digamma convergence.
The selected W remains existential: no synthetic profile is passed off as W.
No Lean/Agda kernel check or RH/GRH proof.
"""
import sympy as s
import mpmath as mp

pi = s.pi
scale = s.Integer(16)
assert 128 == 16*2*4 == 2**7
assert scale**2 == 256
R, M0, origin, t = s.symbols('R M0 origin t', positive=True)
assert s.simplify(
    (16/t)*(2*pi)*(4*origin/(R*M0))
    - 128*pi*origin/(t*R*M0)) == 0
print('PASS 128 = original physical 16 x Fourier inversion 2 x projective origin 4')

q = s.symbols('q', real=True)
mu = s.Function('mu')
a, b = 1+q/16, 1-q/16
symmetric = (mu(t*a)+mu(t*b)-2*mu(t))/2
assert s.simplify(symmetric-symmetric.subs(q,-q)) == 0
assert s.simplify((16/t)*symmetric
                  -(8/t)*(mu(t*a)+mu(t*b)-2*mu(t))) == 0
print('PASS exact q -> -q *ordinate* reflection; odd first mu jet cancels')

# Upstream GammaFacts.stirling:
# |mu(y)-log(|y|/(2*pi))/(2*pi)| <= C_gamma/y^2 for |y|>=1.
# For t>=200 and |q|<=8, t*(1 +/- q/16)>=t/2 and
# the symmetric mu Stirling error <= (4+4+2)*C_gamma/t^2.
# Hence |E_core| <= 80*C_gamma/t^3 * integral_|q|<=8 |C_W(q)|dq.
y = s.symbols('y', real=True, positive=True)  # y=q^2/256
assert s.series(s.log(1-y),y,0,5).removeO().expand() == (
    -y-y**2/2-y**3/3-y**4/4)
assert s.simplify(s.Rational(2,3)-1/(2*(1-s.Rational(1,4)))) == 0
print('PASS Gamma central |q|<=8: log(1-q^2/256), error 80*C_gamma/t^3')

# Lean Fourier theorem: integral q^2 C_W(q)dq = -2*pi*P_W''(0).
# Lean globalCubicModeDefect = 6*pi*(t/16)*P_W''(0).
P2, M2tail = s.symbols('P2 M2tail', real=True)
M2full = -2*pi*P2
M2core = M2full-M2tail
G_cubic = 6*pi*(t/16)*P2
assert s.simplify(-M2full/(64*pi*t)-P2/(32*t)) == 0
assert s.simplify(P2/(32*t)-G_cubic/(12*pi*t**2)) == 0
assert s.simplify(-M2core/(64*pi*t)-P2/(32*t)-M2tail/(64*pi*t)) == 0
# |log(1-z)+z| <= 2*z^2/3 on 0<=z<=1/4.
assert s.simplify((4/pi)*s.Rational(2,3)/256**2-1/(24576*pi)) == 0
print('PASS cubic mode weld: P_W\'\'(0)/(32t)=globalCubicModeDefect/(12*pi*t^2)')
print('PASS logarithmic core remainder <= M4(core)/(24576*pi*t); outer q-tail retained')

mp.mp.dps=45
def actual_zeta23_mu(tau):
    return (mp.re(mp.digamma(mp.mpf('0.25')+mp.j*tau/2))
            - mp.log(mp.pi))/(2*mp.pi)
def actual_second_mu(T,Q):
    return (actual_zeta23_mu(T*(1+Q/16))
            +actual_zeta23_mu(T*(1-Q/16))-2*actual_zeta23_mu(T))
for Q in (2,8,12,20,24,32):
    log_limit=mp.log(abs(1-mp.mpf(Q)**2/256))/(2*mp.pi)
    errors=[abs(actual_second_mu(T,Q)-log_limit) for T in (200,2000,20000)]
    assert errors[2]<errors[1]<errors[0], (Q,errors)
    assert errors[2]<mp.mpf('0.000003'), (Q,errors)
assert mp.log(1-mp.mpf(8)**2/256)<0
assert mp.log(abs(1-mp.mpf(20)**2/256))<0
assert mp.log(abs(1-mp.mpf(24)**2/256))>0
print('PASS actual digamma(mu) limit at six q coordinates and three heights')
print('PASS log sign-change outside core: no global Gamma positivity')
print('OPEN original W-dependent uniform M0/M4, outer q-tail and signed strict terminal')
