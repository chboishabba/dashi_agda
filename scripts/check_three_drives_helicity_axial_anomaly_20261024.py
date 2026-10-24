#!/usr/bin/env python3
"""Three independently driven transverse EM modes, exact helicity/ABJ gates.

They are analytic periodic 3D Beltrami mode fields, NOT localized plasma balls.
One massless charge-e Dirac fermion, periodic/no-flux domain, no axial losses.
Established primary mathematics: Maxwell helicity evolution and ABJ anomaly.
No wormhole negative stress or gravity source is established by this checker.
"""
import sympy as s
x,y,z,k,t,w,a,e,volume=s.symbols('x y z k t omega a e volume',real=True,positive=True)
coords=(x,y,z)
def curl(v):
    return s.Matrix([s.diff(v[2],y)-s.diff(v[1],z),
      s.diff(v[0],z)-s.diff(v[2],x),s.diff(v[1],x)-s.diff(v[0],y)])
modes=[s.Matrix([0,s.sin(k*x),s.cos(k*x)]),
       s.Matrix([s.cos(k*y),0,s.sin(k*y)]),
       s.Matrix([s.sin(k*z),s.cos(k*z),0])]
for v in modes:
    assert all(s.trigsimp(f)==0 for f in (curl(v)-k*v))
    assert s.simplify(sum(s.diff(v[i],coords[i]) for i in range(3)))==0
f=[a*s.cos(w*t+i*2*s.pi/3) for i in range(3)]
norm=s.trigsimp(sum(v*v for v in f))
assert s.simplify(norm-3*a*a/2)==0
H=k*volume*norm
EB=-k*volume*sum(v*s.diff(v,t) for v in f)
assert s.trigsimp(s.diff(H,t)+2*EB)==0
assert s.trigsimp(EB)==0 # rotating but no net integrated axial pump
env=s.Function('envelope')(t)
fe=[env*s.cos(w*t+i*2*s.pi/3) for i in range(3)]
Henv=s.trigsimp(k*volume*sum(v*v for v in fe))
EBenv=s.trigsimp(-k*volume*sum(v*s.diff(v,t) for v in fe))
assert s.simplify(Henv-3*k*volume*env**2/2)==0
assert s.simplify(EBenv+3*k*volume*env*s.diff(env,t)/2)==0
# dQ5/dt = e^2/(2pi^2) int E·B, one massless Dirac flavor.
# Closed-domain anomaly/helicity combination is conserved.
Q5rate=e*e/(2*s.pi**2)*EBenv
assert s.simplify(Q5rate+e*e/(4*s.pi**2)*s.diff(Henv,t))==0
print('PASS: divergence-free 3-mode Beltrami Maxwell fields')
print('PASS: perfect 120-degree phase drive: net helicity / axial pump zero')
print('PASS: amplitude-envelope drive: nonzero E.B with anomaly/helicity balance')
print('OPEN: localized actual plasma, in-in Dirac state, renormalized stress and metric')
