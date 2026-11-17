#!/usr/bin/env python3
"""Exact 12-point rational azimuthal cubature for original KSW F8 TT.

Original fourth-order P Q P - P tr(PQ)/2 source retained. This is
a Fourier angular projector at the axial receiver, not FV PDE proof.
"""
import sympy as s
from itertools import product
x,r=s.symbols('x r',real=True)
y,z=s.symbols('y z',real=True)
card=[(s.Integer(a),s.Integer(b)) for a,b in ((1,0),(-1,0),(0,1),(0,-1))]
diag=[(s.Rational(a,5),s.Rational(b,5))
      for a,b in product((3,-3),(4,-4))]
diag += [(s.Rational(a,5),s.Rational(b,5))
         for a,b in product((4,-4),(3,-3))]
wc=s.Rational(527,4608)
wd=s.Rational(625,9216)
nodes=[(a,b,wc) for a,b in card]+[(a,b,wd) for a,b in diag]
assert len(nodes)==12 and sum(w for a,b,w in nodes)==1
checks=0
for i in range(5):
    for j in range(5-i):
        actual=sum((w*a**i*b**j for a,b,w in nodes),s.S.Zero)
        target=(s.factorial(i)*s.factorial(j)/
                (4**((i+j)//2)*s.factorial(i//2)*s.factorial(j//2)*
                 s.factorial((i+j)//2))) if i%2==j%2==0 else s.S.Zero
        assert actual==target,(i,j,actual,target)
        checks+=1
k=s.Matrix([x,y,z]);sq=k.dot(k)
P=sq*s.eye(3)-k*k.T
Q=s.diag(0,1,-1)
T=(P*Q*P-s.Rational(1,2)*P*s.trace(P*Q)).applyfunc(s.expand)
A=((x*x+r*r)**2+6*(x*x+r*r)*x*x+x**4)/8
for i in range(3):
    for j in range(i,3):
        value=s.factor(sum((w*T[i,j].subs({y:r*a,z:r*b}) for a,b,w in nodes),s.S.Zero))
        expected=A if (i,j)==(1,1) else -A if (i,j)==(2,2) else 0
        assert s.simplify(value-expected)==0,(i,j,value,expected)
        checks+=1
cardYY=sum(T[1,1].subs({y:r*a,z:r*b}) for a,b in card)/4
assert s.simplify(cardYY-A-r**4/8)==0
print(f"{checks}/21 angular moment and six-component tensor projection checks PASS")
print("Extra negative control PASS: four-cardinal yy alias = r^4/8")
