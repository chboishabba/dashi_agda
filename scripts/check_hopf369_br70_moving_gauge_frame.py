#!/usr/bin/env python3
"""BR70 actual MOVING ADM wall covector: tangential vs unit normal gauge.

Full unit normal n^mu = g^mu nu F_nu/sqrt(g^-1(dF,dF)), F=n-f(t,x,y,z).
The physical unit-normal scalar gauge component is C_perp=n^mu C_mu.
The actual tangential pullback is c_a=e_a^mu C_mu=C_a+f_a C_n.
Covector C_n (coordinate) must NOT be mistaken for physical C_perp
away from the compatible Gaussian wall. Both plus/minus physical faces,
all five covector entries and all four wall tangent directions survive.

The exact independent reconstruction is C_mu =
  c_a (dx^a)_mu + C_perp n_mu plus appropriate normal/tangent dual;
for any non-characteristic F the 5x5 map [e_a^mu; n^mu] is invertible
on the physical wall. This is a geometric basis change, not a Bianchi
evolution theorem or a positivity theorem for an indefinite inner product.

--part frame|shift|negative
"""
import argparse
import sympy as s

def make():
    # ADM with diagonal positive spatial H and independent shift v,
    # moving planar material graph with nonzero time and tangential tilt.
    N=s.Rational(3,2)
    h=s.diag(1,s.Rational(5,4),s.Rational(6,5),s.Rational(4,3))
    v=s.Matrix([s.Rational(1,11),s.Rational(-1,13),
                s.Rational(2,17),s.Rational(1,19)])
    hi=h.inv()
    Gi=(-s.Matrix([[1/N**2]])).row_join((v/N**2).T)
    Gi=Gi.col_join((v/N**2).row_join(hi-v*v.T/N**2))
    df=s.Matrix([s.Rational(1,7),s.Rational(-1,9),
                 s.Rational(2,11),s.Rational(1,13)])
    F=s.Matrix([-a for a in df]+[1])
    z=s.cancel((F.T*Gi*F)[0])
    assert z>0
    E=s.Matrix(5,4,lambda mu,a:int(mu==a)+(df[a] if mu==4 else 0))
    normal=Gi*F/s.sqrt(z)
    T=E.T.col_join(normal.T)
    return Gi,E,F,z,normal,T

def frame():
    Gi,E,F,z,normal,T=make()
    C=s.Matrix(s.symbols('C0:5'))
    measured=T*C
    inverse=T.inv()
    assert (inverse*measured-C).applyfunc(s.simplify)==s.zeros(5)
    tangent=E.T*C
    assert tangent==C[:4,0]+s.Matrix([E[4,i]*C[4] for i in range(4)])
    assert (normal.T*F)[0]==s.sqrt(z)
    assert s.simplify((normal.T*Gi.inv()*normal)[0]-1)==0
    assert s.simplify((T.det())/s.sqrt(z))!=0
    print("BR70 exact 5x5 moving physical gauge frame invertibility and bidirectional reconstruction")

def shift():
    Gi,E,F,z,normal,T=make()
    Cp=s.Matrix(s.symbols('Cp0:5'))
    Cm=s.Matrix(s.symbols('Cm0:5'))
    plus=T*Cp;minus=T*Cm
    # Full gauge continuity is a source condition, not a statement that
    # the reference D/E prefixes become identical.
    tangJump=plus[:4,0]-minus[:4,0]
    normalJump=plus[4]-minus[4]
    assert (tangJump-E.T*(Cp-Cm)).applyfunc(s.simplify)==s.zeros(4)
    assert s.simplify(normalJump-(normal.T*(Cp-Cm))[0])==0
    # The original BR34 reference c_n at Gaussian F=n is different
    # from physical n·C in a tilted/shifting material chart.
    assert s.simplify(normal[4]-1)!=0
    assert T.shape==(5,5)
    print("BR70 full both-side physical gauge tangent and normal channels, nonzero mixing")

def negative():
    Gi,E,F,z,normal,T=make()
    C=s.Matrix([1,2,3,4,5])
    physical=(T*C)[4]
    coordinate=C[4]
    assert s.simplify(physical-coordinate)!=0
    wrong=E.T*C
    assert wrong!=C[:4,0]
    # At z=0, unit normal has no inverse; at z<0 real spacelike
    # normalization also fails. Require a positive physical witness.
    print("BR70 negative controls: coordinate-normal and tangent projection refused")

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=['frame','shift','negative'],default='frame')
    x=p.parse_args();{'frame':frame,'shift':shift,'negative':negative}[x.part]()
if __name__=='__main__':main()
