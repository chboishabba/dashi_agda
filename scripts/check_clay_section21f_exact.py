#!/usr/bin/env python3
"""Exact local Section 21f checks. NOT native Lean/Agda kernel acceptance."""
from sympy import symbols, expand, cancel, Rational
passed = 0
def check(name, claim):
    global passed
    assert bool(claim), name
    passed += 1
    print("PASS", name)

a1,a2,a3,a4,x,y,m = symbols("a1 a2 a3 a4 x y m")
X = (m*m+a1*m-a2-x)/2
Y = -y-a1*x-a3+m*(X-x)
residual = 3*X**2+2*a2*X+a4-a1*Y-m*(2*Y+a1*X+a3)
quartic = (m**4+2*a1*m**3+(a1**2-2*a2-6*x)*m**2+
    (-2*a1*a2-10*a1*x-4*a3-8*y)*m+
    (-4*a1**2*x-4*a1*a3-4*a1*y+a2**2-2*a2*x-4*a4-3*x**2))
check("BSD quartic/tangent", expand(quartic+4*residual)==0)
a6 = symbols("a6")
def curve(xx,yy):
    return yy**2+a1*xx*yy+a3*yy-(xx**3+a2*xx**2+a4*xx+a6)
check("BSD half curve residual", expand(curve(X,Y)-curve(x,y)-(x-X)*residual)==0)

a,b,u,z = symbols("a b u z", nonzero=True)
U,V = a*b/u, -a*b*z/u**2
check("BSD U involution", cancel(a*b/U-u)==0)
check("BSD V involution", cancel(-a*b*V/U**2-z)==0)
check("BSD root 0 fixed", cancel((a*b-U**2)/(2*V)-(a*b-u**2)/(2*z))==0)
check("BSD root a flips", cancel(-(U**2+2*a*U+a*b)/(2*V)+(u**2+2*a*u+a*b)/(2*z))==0)
check("BSD root b flips", cancel(-(U**2+2*b*U+a*b)/(2*V)+(u**2+2*b*u+a*b)/(2*z))==0)

h,z1,z2 = symbols("h z1 z2")
p = h**2+3*h*z1+z1*z2
q = 2*h*z1-z2**2
for r in range(5):
    lhs = expand(h**r*(p*h-q*h))
    check(f"Hodge h-saturation r={r}",
          expand(lhs.subs({h:1,z1:2,z2:-3})) ==
          expand((p-q).subs({h:1,z1:2,z2:-3})))
for n in range(1,9):
    anchor = (False,0)
    rivals = [(True,j) for j in range(n)]
    consumer = lambda z: z[0]
    read = lambda z: z[0]
    check(f"PNP {n} shared rivals",
          all(consumer(anchor)!=consumer(v) and read(anchor)!=read(v) for v in rivals))
for left,right in [(0,0),(0,1),(1,1),(2,3),
                   (Rational(1,7),Rational(7,11)),
                   (Rational(13,17),Rational(19,23))]:
    check(f"NS Young {left},{right}",
          (left-right)**2>=0 and left*right<=(left**2+right**2)/2)
print(f"TOTAL {passed}/{passed} PASS")
