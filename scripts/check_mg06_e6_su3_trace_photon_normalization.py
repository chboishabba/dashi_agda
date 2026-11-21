#!/usr/bin/env python3
"""MG06 source-trace E6/trinification photon normalization backsolve.
Donors: #1106 E6 first-Tits charge generators; #1241 E32/E33/E21
gauge Cartan and 27-state source; recent #1531 3-family and same-connection
gates. This is a CONDITIONAL equal SU(3)^3 coupling normalization,
not a completed globally anomaly-free 5D theory or empirical prediction.
"""
import sympy as s
from itertools import product

H_L=s.diag(s.Rational(1,2),-s.Rational(1,2),0)
U_L=s.diag(-1,-1,2)
U_R=s.diag(-1,-1,2)
H_R=s.diag(1,-1,0)
Q=s.Matrix([1,s.Rational(1,6),s.Rational(1,6),-s.Rational(1,2)])
Y=Q-s.Matrix([1,0,0,0])
phi=s.Matrix([0,2,1,1])
chi=s.Matrix([0,2,-2,0])
ew=s.Matrix([-s.Rational(1,2),-1,1,-1])
gs=chi/2

def tr(M):
    return sum(M[j,j] for j in range(M.rows))

def matter():
    parity=(-1,-1,1)
    out=[]
    for c,l in product(range(3),repeat=2):
        out.append((-parity[l],s.Matrix([-H_L[l,l],-U_L[l,l],0,0])))
    for c,r in product(range(3),repeat=2):
        out.append((-parity[r],s.Matrix([0,0,U_R[r,r],H_R[r,r]])))
    for l,r in product(range(3),repeat=2):
        out.append((-parity[l]*parity[r],
                    s.Matrix([H_L[l,l],U_L[l,l],-U_R[r,r],-H_R[r,r]])))
    return out

def main():
    # Gauge action -Tr(F_AB F^AB)/(2g5^2), separately in SU3L and SU3R:
    # in component -F_i F_j K_ij/(4 g5^2), K_ij=2 Tr(T_i T_j).
    K=s.diag(*(2*tr(t*t) for t in (H_L,U_L,U_R,H_R)))
    assert K==s.diag(1,12,12,4)
    assert tr(H_L*U_L)==0 and tr(H_R*U_R)==0
    assert (Q.T*K*Q)[0]==s.Rational(8,3)
    assert (Y.T*K*Y)[0]==s.Rational(5,3)
    assert (Q.T*K*s.Matrix([1,0,0,0]))[0]==1
    mass=sum((t*t.T for t in (phi,chi,gs,ew)),s.zeros(4))
    assert mass.rank()==3 and len(mass.nullspace())==1
    assert mass*Q==s.zeros(4,1)
    g5,L=s.symbols('g5 L',positive=True)
    g4=g5/s.sqrt(L)
    e4=g4/s.sqrt((Q.T*K*Q)[0])
    assert s.simplify(e4-s.sqrt(s.Rational(3,8))*g4)==0
    assert s.simplify((e4/g4)**2-s.Rational(3,8))==0
    # Old illustrative identity K=I is not the source SU3 trace norm.
    assert (Q.T*Q)[0]==s.Rational(47,36)
    assert (Q.T*Q)[0]!=(Q.T*K*Q)[0]
    states=matter()
    assert len(states)==27
    assert (sum(p==1 for p,_ in states),sum(p==-1 for p,_ in states))==(16,11)
    charges=[(q.T*Q)[0] for _,q in states]
    allowed={s.Rational(-1),s.Rational(-2,3),s.Rational(-1,3),
             s.Integer(0),s.Rational(1,3),s.Rational(2,3),s.Integer(1)}
    assert set(charges).issubset(allowed)
    assert {s.Integer(-1),s.Rational(2,3),s.Rational(-1,3),s.Integer(0)}.issubset(set(charges))
    assert all((3*z).q==1 for z in charges)
    assert all((q.T*Q)[0] == (q.T*Y)[0]+q[0] for _,q in states)
    assert len(s.diag(mass,s.zeros(1)).nullspace())==2
    # A positive kinetic mixing modifies normalization but not the Higgs nullity.
    for alpha in (s.Rational(1,2),s.Integer(2)):
        Km=K.copy()
        Km[1,2]=Km[2,1]=alpha
        assert Km.is_positive_definite
        assert s.simplify((Q.T*Km*Q)[0]-s.Rational(8,3)-alpha/18)==0
        assert mass.rank()==3
    print('PASS canonical source SU3 trace K=diag(1,12,12,4); Y norm 5/3; Q norm 8/3')
    print('PASS conditional common-coupling e4=sqrt(3/8)g5/sqrt(L), sin²thetaW=3/8 at matching scale')
    print('PASS 27 original matter state charges and 16L/11R source parities')
    print('PASS independent Maxwell and uncalibrated kinetic-mixing negative controls')
    print('OPEN same-action universal coupling, normalizable photon, global anomaly, quantum stress, physical spectrum')

if __name__=='__main__':
    main()
