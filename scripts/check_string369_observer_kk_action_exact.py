#!/usr/bin/env python3
"""Exact observer-dependent compact-circle scalar field reduction.
CLASSICAL: Kaluza, Klein, Fourier/KK orthogonality and mode truncation.
EXISTING DASHI: CalabiYau369CompactFibreBridge, TriadicDepthOneCharacters,
BalancedTernaryFourierModeExact, U1SU2GroupTorusExact and TOE physical cutset.
NEW: explicit first-band action and C3 sampling/alias negative control.
USER: visible dimensions and charges may depend on observer resolution.
ChatGPT-assisted. No CY3, string worldsheet, SM fermions or physical TOE claim.
"""
import sympy as s

theta,R,kappa,A,mu=s.symbols('theta R kappa A mu',positive=True,real=True)
u,v,w,du,dv,dw=s.symbols('u v w du dv dw',real=True)
N=s.sqrt(2*s.pi*R)
phi=(u+s.sqrt(2)*v*s.cos(theta)+s.sqrt(2)*w*s.sin(theta))/N
# Same 5D KK metric ds5²=g4+R²(dtheta+kappa*A)^2.
horizontal=(du+s.sqrt(2)*(dv-kappa*A*w)*s.cos(theta)
           +s.sqrt(2)*(dw+kappa*A*v)*s.sin(theta))/N
vertical=s.diff(phi,theta)/R
integrate=lambda ex:s.simplify(R*s.integrate(
    s.expand_trig(s.expand(ex)),(theta,0,2*s.pi)))
assert s.simplify(integrate(phi**2)-(u*u+v*v+w*w))==0
assert s.simplify(integrate(horizontal**2)-
    (du**2+(dv-kappa*A*w)**2+(dw+kappa*A*v)**2))==0
assert s.simplify(integrate(vertical**2)-(v*v+w*w)/R**2)==0
assert s.simplify(integrate(mu**2*phi**2)-mu**2*(u*u+v*v+w*w))==0
# Reduced mass squares: m0²=mu²; m±1²=mu²+R^-2.
# Horizontal derivatives: Dv=dv-kappa*A*w; Dw=dw+kappa*A*v.
alpha=s.symbols('alpha',real=True)
rotation=s.Matrix([[s.cos(alpha),s.sin(alpha)],
                   [-s.sin(alpha),s.cos(alpha)]])
J=s.Matrix([[0,-1],[1,0]])
assert s.simplify(rotation.T*rotation-s.eye(2))==s.zeros(2)
assert s.simplify(rotation*J-J*rotation)==s.zeros(2)
# C3 samples, algebraically identical to finite three-cycle character band.
samples=[s.expand((N*phi).subs(theta,2*s.pi*j/3)) for j in range(3)]
assert s.simplify(sum(samples)/3-u)==0
assert s.simplify(sum(z*z for z in samples)/3-(u*u+v*v+w*w))==0
vec=s.Matrix(samples)
L=s.Matrix([[2,-1,-1],[-1,2,-1],[-1,-1,2]])
assert all(s.simplify(z)==0 for z in
           L*vec-3*(vec-u*s.ones(3,1)))
# Single first-band matching condition: discrete spacing²=3R².
assert s.simplify((vec.T*L*vec)[0]/(3*(3*R**2))
    -(v*v+w*w)/R**2)==0
# C3 cannot distinguish continuum frequencies n and n+3.
n,j=s.symbols('n j',integer=True)
assert s.simplify(s.exp(2*s.pi*s.I*(n+3)*j/3)-
                  s.exp(2*s.pi*s.I*n*j/3))==0
print('PASS: exact S1 n=0,+1,-1 norm and gauge-covariant action')
print('PASS: 4D masses mu², mu²+R^-2 and charge rotation algebra')
print('PASS: C3 Parseval, graph Laplacian eigenvalue 3 and first-band match')
print('PASS: n versus n+3 alias proves finite 369 loses high KK modes')
print('OPEN: physical CY3/string, SM chirality, GRQFT same-action, observer calibration')
