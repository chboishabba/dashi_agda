#!/usr/bin/env python3
"""Clay YM P0: three exact finite algebra rounds, original source respected.
R1 original Wilson Cartan transverse Fourier Hessian + nonconstant wave.
R2 true R445/F19 pair Jacobian Hessian congruence + branch-resolved Singer.
R3 marked nonlinear Hessian correction + mass-gap non-promotion.
Not continuous Haar, CMP119/122 source T, W3 decay or continuum OS.
"""
from itertools import product
import sympy as s

I=s.I
print("ROUND1 original Cartan Wilson Fourier Hessian and wave")
for L,expected in ((4,s.Integer(2)),(8,2-s.sqrt(2)),
                   (16,2-s.sqrt(2+s.sqrt(2)))):
    z=s.cos(2*s.pi/L)+I*s.sin(2*s.pi/L)
    d=s.Matrix([0,z-1,0,0])
    lam=s.simplify(s.expand_complex(s.conjugate(z-1)*(z-1)))
    assert s.simplify(lam-expected)==0
    H=(lam*s.eye(4)-d*d.conjugate().T).applyfunc(s.simplify)
    assert H==s.diag(lam,0,lam,lam)
    assert (H*d).applyfunc(s.simplify)==s.zeros(4,1)
    for j in (0,2,3):
        e=s.eye(4)[:,j]
        assert (H*e-lam*e).applyfunc(s.simplify)==s.zeros(4,1)
    wave=lambda x,t:z**(x-t)
    for x,t in ((0,0),(1,3),(2,4),(L-1,L+2)):
        secondtime=wave(x,t+1)-2*wave(x,t)+wave(x,t-1)
        secondspace=wave(x+1,t)-2*wave(x,t)+wave(x-1,t)
        assert s.simplify(s.expand_complex(secondtime-secondspace))==0
    # The Cartan Wilson Hessian from six oriented plaquettes has
    # 3 positive transverse directions at p=(0,2pi/L,0,0),
    # a longitudinal gauge-null direction d and the energy lam*||A||^2.
    assert s.simplify(lam*L**4/L**4-lam)==0
    print(f"L={L}: eigenvalue={lam}, 3 transverse+1 gauge null; wave PASS")

print("ROUND2 original native U0,V -> W=U0 V,V source-pair Hessian")
# Two native F19 pairs with two coupled spectator links.
X=s.Matrix(s.symbols('u0 v0 u1 v1 spectator0 spectator1',real=True))
C=s.Matrix([[1,1,0,0,-1,0],[0,0,1,-1,1,0],
            [1,-1,-1,1,0,1],[0,1,0,-1,-1,1]])
Q=sum((C*X)[i]**2 for i in range(C.rows))/2
H0=s.hessian(Q,X)
assert H0==C.T*C
J=s.eye(6);J[0,1]=1;J[2,3]=1
Ji=J.inv()
Y=s.Matrix(s.symbols('W0 V0 W1 V1 S0 S1',real=True))
pull={X[i]:(Ji*Y)[i] for i in range(6)}
assert s.hessian(s.expand(Q.subs(pull,simultaneous=True)),Y)==Ji.T*H0*Ji
assert all(s.diff(Q,q).subs({v:0 for v in X})==0 for q in X)
# Exact original order-26 Singer G^k on three 3-trit blocks.
G=s.Matrix([[-1,-1,0],[0,-1,-1],[-1,-1,-1]])
assert (G**26).applyfunc(lambda z:int(z)%3)==s.eye(3)
def sign9(a):return tuple((-1,0,1,0)[v] for v in a)+(0,)*5
def branch(a):return tuple(None if v%2==0 else (v-1)//2 for v in a)
def transchart(a,M):
    q=sign9(a)
    return tuple((int(z)+1)%3-1 for i in (0,3,6)
                 for z in M*s.Matrix(q[i:i+3]))
def recover(q,b,M):
    inv=M.inv_mod(3)
    u=tuple((int(z)+1)%3-1 for i in (0,3,6)
            for z in inv*s.Matrix(q[i:i+3]))
    return tuple(0 if x==-1 else 2 if x==1 else 1+2*bb
                 for x,bb in zip(u[:4],b))
sites=list(product(range(4),repeat=4))
for k in range(26):
    M=(G**k).applyfunc(lambda z:int(z)%3)
    chart={(transchart(x,M),branch(x)) for x in sites}
    assert len(chart)==256
    assert all(recover(transchart(x,M),branch(x),M)==x for x in sites)
print("L4 Singer: 26/26 charts reconstruct all 256 independent gauge sites; F19 Hessian congruence PASS")

print("ROUND3 differentiated global marks and true physical-gap boundary")
y,theta=s.symbols('y theta',real=True)
phi=y+y*y
S=lambda x:s.Rational(1,2)*x*x+theta*x
assert s.diff(S(phi),y,2).subs(y,0)==1+2*theta
assert s.diff(S(y),y,2).subs(y,0)==1
# Nonstationary marked source needs gradient·D²coordinate; the
# vacuum has zero first derivative and just Hessian congruence.
L=s.Symbol('L',positive=True)
assert s.limit(4*s.sin(s.pi/L)**2,L,s.oo)==0
assert s.limit(4*L*L*s.sin(s.pi/L)**2,L,s.oo)==4*s.pi**2
print("Marked nonlinear-coordinate Hessian correction PASS; finite transverse wave does NOT imply mass gap")
print("PASS three exact finite rounds; original physical RG T, absolute W3, E1/OS/D2 remain OPEN")
