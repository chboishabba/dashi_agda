"""Conditional massless KK disk and driven phase rectification inverse.
Standard scalar-tensor charge convention; no calibrated superconducting source.
"""
import math
import sympy as s
from scipy.special import j0
G=6.67430e-11;c=299792458.;g=9.80665;R=.1375;z=.1
b=-1/math.sqrt(6); shape=1-z/math.hypot(R,z)
M=3*g*R**2/(2*G*shape)
# Scalar charge Q=dE/dtheta, in joules. Acceleration toward disk is
# 4G beta_probe Q/(c² R²) * shape, for uniform thin disk.
Q=M*c*c*b
assert math.isclose(4*G*b*Q*shape/(c*c*R**2),g)
print('shape',shape,'equivalent mass kg',M,'signed scalar charge J',Q)
for beta in [-1/math.sqrt(6),-10,-100]:
    E=Q/beta
    print('beta',beta,'required mean phase potential J',E,'J0 at amplitude 1 rad',E/(1-j0(1)))
# Fixed phase static source, and relaxed curvature for a supported phase.
t,r,J,beta,F,k=s.symbols('t r J beta F k',real=True)
V=J*s.exp(beta*t)*(1-s.cos(r))-F*r+k*t*t/2
K=s.hessian(V,(t,r)).subs(t,0)
assert s.simplify(s.diff(V,t).subs(t,0)-beta*J*(1-s.cos(r)))==0
schur=s.simplify(K[0,0]-K[0,1]**2/K[1,1])
assert s.simplify(schur-(k+beta**2*J*(1-1/s.cos(r))))==0
print('relaxed curvature',schur,'stability requires k > beta² J (sec r - 1) for cos r > 0')
# No divergence in source as phase softens to pi/2
assert s.limit(s.diff(V,t).subs(t,0),r,s.pi/2)==beta*J
# available excitation benchmark from earlier illustrative ring
E=2073.; print('required |beta| for 2073 J',abs(Q)/E)
print('PASS sign, disk inverse, rectifier and Schur complement')
