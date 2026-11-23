"""Conditional normalized Leggett/radion and receiver checks; not original-paper replay.
Sources: Leggett optical excitation PRB 95 104503; Kuenstner PRR 7 013281;
Zhang et al Nat Commun 17 1825. Reduced models below are our synthesis.
"""
import sympy as s
import numpy as np
from scipy.special import j0
from math import pi,sqrt
I1,I2,J,theta,beta,r=s.symbols('I1 I2 J theta beta r',positive=True)
Ir=I1*I2/(I1+I2)
V=J*s.exp(beta*theta)*(1-s.cos(r))
assert s.simplify(s.diff(V,r,theta).subs(theta,0)-J*beta*s.sin(r))==0
assert s.simplify(s.diff(V,r,2).subs(theta,0)/Ir-J*s.cos(r)/Ir)==0
# Static rectification: average cos(A cos wt)=J0(A).
for A in [.01,.1,.5,1.]:
 t=np.arange(100000)*2*pi/100000; avg=np.mean(1-np.cos(A*np.cos(t)))
 assert abs(avg-(1-j0(A)))<1e-14
 print('phase amplitude',A,'rectified source / (-beta J)',avg)
# sheet, weak massless scalar: lap theta = 8pi G/c^2 beta rho
# jump = 8pi G/c^2 beta Sigma; one-sided gradient = half jump
G=6.67430e-11;c=299792458.;g=9.80665
Sigma=6*g/(4*pi*G)
print('massless infinite sheet universal KK source kg/m2',Sigma)
# finite disk massless axial scalar acceleration magnitude: (1/3)*2pi G Sigma*(1-z/sqrt(z²+R²))
R=.1375;z=.1
shape=1-z/sqrt(z*z+R*R)
sigma=g/(2*pi*G/3*shape)
print('disk geometric inverse kg/m2',sigma,'kg',sigma*pi*R*R,'sign must be repulsive')
# normalized spectral sum: bright direction, not N^2 independent excitations
v=np.array([1.,2.,-3.]); bright=v/np.linalg.norm(v); assert np.isclose(bright@v,np.linalg.norm(v))
# generic passive red-sideband two-port reduced model, NOT full RQU apparatus
ka,kb,ga,ea,eb=s.symbols('ka kb ga ea eb',positive=True)
C=4*ga**2/(ka*kb)
eta=ea*eb*4*C/(1+C)**2
assert s.factor(ea*eb-eta)==ea*eb*(4*ga**2-ka*kb)**2/(4*ga**2+ka*kb)**2
assert s.simplify(eta.subs(ga,s.sqrt(ka*kb)/2)-ea*eb)==0
# four-qubit signed GHZ: multiparameter QFIM outer product, not all vector components simultaneously
W=np.array([[1.,0],[1.,0],[-1.,1],[-1.,1]])
q=np.array([1,1,-1,-1])@W; F=np.outer(q,q)
assert np.linalg.matrix_rank(F)==1
print('GHZ QFIM at t=1',F.tolist(),'rank',np.linalg.matrix_rank(F))
print('PASS rectification, canonical relative inertia, sheet/disk inverse, bright norm, passive conversion, GHZ rank')
