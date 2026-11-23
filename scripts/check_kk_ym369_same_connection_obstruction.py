#!/usr/bin/env python3
"""Exact same-connection discriminator, independently executable.

Classical: BPST SU(2) self-dual instanton (Belavin, Polyakov, Schwartz,
Tyupkin 1975); 5D KK Taub-NUT/Gross-Perry-Sorkin U(1) connection.
Existing DASHI: BalabanSU2LieBracket [X,Y]=2 X cross Y;
U1SU2GroupTorusExact Cartan subgroup; source-backed CMP109 spatial C3.
New: exact two-curvature noncommutation witness versus U(1) embedding.
The result is a NO-GO for a gauge-equivalent literal identification of
these two specific connections, not for a coupled SU2+KK 5D solution.
"""
import sympy as s

rho,m,theta=s.symbols('rho m theta',positive=True,real=True)
# Quaternion imaginary Lie basis [e_a,e_b] = 2 epsilon_abc e_c.
e1=s.Matrix([1,0,0]); e2=s.Matrix([0,1,0]); e3=s.Matrix([0,0,1])
def bracket(u,v): return 2*u.cross(v)
# BPST regular-gauge F^a_mn=-4 rho^2 eta^a_mn / (|x|^2+rho^2)^2.
# At x=0: eta^3_12=+1, eta^2_13=-1.
F12=-4*e3/rho**2
F13= 4*e2/rho**2
comm=bracket(F12,F13)
assert all(s.simplify(z-t)==0 for z,t in zip(comm,32*e1/rho**4))
assert s.simplify(comm.dot(comm)-1024/rho**8)==0
# KK abelian curvature: da = -(1/2) sin(theta) dtheta ^ dphi,
# and its fixed su2 Cartan embedding is F(2-form) * e3.
KKthetaPhi=-s.sin(theta)*e3/2
KKother=(1+m)*e3
assert bracket(KKthetaPhi,KKother)==s.zeros(3,1)
# C3 covariance of cross bracket is a consequence of det(P)=+1.
P=s.Matrix([[0,0,1],[1,0,0],[0,1,0]])
assert P**3==s.eye(3) and P.det()==1
assert bracket(P*F12,P*F13)==P*comm
# Chern number normalized 2pi-period circle: integral F /2pi = -1.
chern=s.simplify((s.integrate(-s.sin(theta)/2,(theta,0,s.pi))*2*s.pi)/(2*s.pi))
assert chern==-1
print('PASS: BPST curvature bracket = (32/rho^4)e1 and squared norm 1024/rho^8 > 0')
print('PASS: every embedded U1 curvature lies in a commuting Cartan line')
print('PASS: oriented C3 covariance of SU2 bracket')
print('PASS: KK first Chern number -1 for the normalized circle connection')
print('NO-GO: no SU2 gauge transformation identifies full BPST curvature with embedded KK-U1')
print('OPEN: coupling, backreaction, physical sector matching, caloron and nonlinear stability')
