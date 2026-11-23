#!/usr/bin/env python3
"""Exact local Taub-NUT Levi-Civita -> chiral SU(2) curvature calculation.

Classical prior work: Gibbons–Hawking (1978); Gross–Perry / Sorkin (1983);
Cartan moving frames, Levi-Civita curvature and Spin(4) chiral split.
DASHI donors: BalabanSU2LieBracket, SU2Bracket369OrientationBridgeExact.
Current bounded contribution: exact selected-point Ricci and chiral curvature
reconstruction from the SAME KK metric; not the independent BPST instanton,
not global YM theory, physical spin/statistics, or continuum Wilson limit.
"""
import sympy as s

x,y,z=s.symbols("x y z",real=True)
xyz=(x,y,z)
r=s.sqrt(x*x+y*y+z*z)
m=s.Integer(1)
V=1+m/r
# Smooth gauge near positive z axis: A=m(1-cos(theta))d(phi).
# Sign is consistent with A=-m*cos(theta)d(phi) up to a patch shift;
# hence dA=+m sin(theta)d(theta)^d(phi).
# It is the orientation-reversed version of the previous negative-charge
# monopole connection, so chiral plus/minus labels depend on this choice.
A=s.Matrix([-m*y/(r*(r+z)),m*x/(r*(r+z)),0,1])
g=s.zeros(4)
for i in range(3):
    g[i,i]=V
for i in range(4):
    for j in range(4):
        g[i,j]+=A[i]*A[j]/V
point={x:0,y:0,z:1}
g0=g.subs(point)
inverse=g0.inv()
def deriv(expr,k):
    return s.diff(expr,xyz[k]).subs(point) if k<3 else s.Integer(0)
D=[[[deriv(g[a,b],k) for k in range(4)] for b in range(4)] for a in range(4)]
DD=[[[[s.diff(g[a,b],xyz[k],xyz[l]).subs(point)
       if k<3 and l<3 else s.Integer(0)
       for l in range(4)] for k in range(4)] for b in range(4)] for a in range(4)]
# Lowered Christoffel and its derivative, at the selected exact point.
L=[[[s.Rational(1,2)*(D[a][b][c]+D[a][c][b]-D[b][c][a])
     for c in range(4)] for b in range(4)] for a in range(4)]
G=[[[sum(inverse[a,d]*L[d][b][c] for d in range(4))
     for c in range(4)] for b in range(4)] for a in range(4)]
DL=[[[[s.Rational(1,2)*(DD[a][b][c][e]+DD[a][c][b][e]-DD[b][c][a][e])
       for e in range(4)] for c in range(4)] for b in range(4)] for a in range(4)]
DI=[[[ -sum(inverse[a,p]*D[p][q][e]*inverse[q,b]
           for p in range(4) for q in range(4))
       for e in range(4)] for b in range(4)] for a in range(4)]
DG=[[[[sum(DI[a][h][e]*L[h][b][c]+inverse[a,h]*DL[h][b][c][e]
           for h in range(4)) for e in range(4)]
     for c in range(4)] for b in range(4)] for a in range(4)]
# R^a_bcd = d_c Gamma^a_db - d_d Gamma^a_cb +
#            Gamma^a_ce Gamma^e_db - Gamma^a_de Gamma^e_cb
R=[[[[s.factor(DG[a][d][b][c]-DG[a][c][b][d]+
           sum(G[a][c][e]*G[e][d][b]-G[a][d][e]*G[e][c][b]
               for e in range(4))) for d in range(4)]
     for c in range(4)] for b in range(4)] for a in range(4)]
Ric=s.Matrix(4,4,lambda b,d:
    s.factor(sum(R[a][b][a][d] for a in range(4))))
# Orthonormal vector frame at the selected point:
# e_i=(1/sqrt(2))partial_i, e_4=sqrt(2)partial_psi.
frame=[1/s.sqrt(2)]*3+[s.sqrt(2)]
Ro=[[[[s.simplify(sum(g0[a,e]*R[e][b][c][d] for e in range(4))
             *frame[a]*frame[b]*frame[c]*frame[d])
      for d in range(4)] for c in range(4)] for b in range(4)] for a in range(4)]
def chi(sign,c,d):
    return s.Matrix([
        s.simplify(Ro[1][2][c][d]+sign*Ro[0][3][c][d]),
        s.simplify(Ro[2][0][c][d]+sign*Ro[1][3][c][d]),
        s.simplify(Ro[0][1][c][d]+sign*Ro[2][3][c][d])])
assert Ric==s.zeros(4)
assert all(chi(-1,i,j)==s.zeros(3,1)
           for i in range(4) for j in range(i+1,4))
assert chi(1,0,1)==s.Matrix([0,0,s.Rational(1,4)])
assert chi(1,0,2)==s.Matrix([0,s.Rational(1,8),0])
assert 2*chi(1,0,1).cross(chi(1,0,2))==s.Matrix([-s.Rational(1,16),0,0])
assert chi(1,0,1)==chi(1,2,3)
assert chi(1,0,2)==-chi(1,1,3)
assert chi(1,0,3)==chi(1,1,2)
print("PASS: Ricci=0 at north-axis point m=r=1, exact tensors")
print("PASS: one chiral su2 curvature sector vanishes")
print("PASS: other chiral sector self-dual and genuinely nonabelian")
print("PASS: commutator (-1/16,0,0) with [u,v]=2 cross")
print("OPEN: global spin bundle/connection, YM identification, stability")

# Generator normalization bridge to Dunajski (2013), section 2:
# his [t_i,t_j]=-(1/2) eps_ijk t_k; native DASHI has [e_i,e_j]=2 eps e_k.
# One exact isomorphism is t_i = -e_i/4 (for matched epsilon orientation).
basis=s.eye(3)
def native_bracket(u,v):
    return 2*u.cross(v)
t=[-basis[:,i]/4 for i in range(3)]
for i,j,k in ((0,1,2),(1,2,0),(2,0,1)):
    assert native_bracket(t[i],t[j])==-s.Rational(1,2)*t[k]
# Under the explicitly stated R_23=R_14 self-dual index convention:
# C_i = R_jk + R_i4 = 2 R_jk, so paper's curvature coefficient
# F^i=(1/2)eps_ijk R_jk=C_i/2 in t_i, hence -C_i/8 in native e_i.
normalized12=-chi(1,0,1)/8
normalized13=-chi(1,0,2)/8
assert normalized12==s.Matrix([0,0,-s.Rational(1,32)])
assert normalized13==s.Matrix([0,-s.Rational(1,64),0])
assert native_bracket(normalized12,normalized13)==s.Matrix([-s.Rational(1,1024),0,0])
print("PASS: Dunajski t_i=-e_i/4 matches native quaternion [e_i,e_j]=2 eps e_k")
print("PASS: matched chiral curvature generator-scaled bracket = -e1/1024")
print("CAUTION: generator normalization does not yet fix physical YM coupling/trace")
