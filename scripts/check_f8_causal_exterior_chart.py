"""F8 original AdS exterior chart and causal zero outer trace, exact geometry.
This is a domain identity, not existence of the coupled evolution.
"""
from fractions import Fraction as Q
from math import factorial
import sympy as s


def run():
    t,n,z=s.symbols('t n z',positive=True)
    theta=s.asinh(t); beta=s.sqrt(1+t**-2); A=s.sinh(theta-n); N=s.cosh(theta-n)/s.cosh(theta)
    P=s.sinh(theta-n); B=s.cosh(theta-n)
    # Use independent positive hyperbolic variables, enforce B²-P²=1.
    p,c,d=s.symbols('p c d',positive=True)
    Tt=d*c*c/p**2; Tn=-1/p**2; zt=-d*c/p**2; zn=c/p**2
    J=s.Matrix([[Tt,Tn],[zt,zn]])
    g=J.T*s.diag(-p*p,p*p)*J
    red=lambda expr:s.factor(s.cancel(expr)).subs(c*c,p*p+1).simplify()
    # General algebraic checks at p=a, c=cosh(theta-n), d=theta_t.
    assert red(g[0,0]+d*d*c*c)==0
    assert red(g[0,1])==0
    assert red(g[1,1]-1)==0
    assert red(J.det()-d*c/p**2)==0
    # Actual coordinate derivatives, using T=theta-coth(theta-n), z=csch(theta-n).
    T=theta-s.coth(theta-n); zz=1/A
    assert s.simplify(s.diff(T,n)+zz**2)==0
    assert s.simplify(s.diff(zz,n)-B/A**2)==0
    assert s.simplify(s.diff(T,t)-B**2/(A**2*s.sqrt(1+t*t)))==0
    assert s.simplify(s.diff(zz,t)+N/A**2)==0
    # Direct chart (t,z) has no GN caustic for finite z, original brane z=1/t.
    T=theta-s.sqrt(1+z*z); g=s.diag(-z**-2,z**-2)
    J=s.Matrix([T.diff(t),T.diff(z),0,1]).reshape(2,2)
    gt=(J.T*g*J).applyfunc(s.simplify)
    assert s.simplify(gt.det()+1/(z**4*(1+t*t)))==0
    assert s.simplify(gt.inv()[0,0]+z*z*(1+t*t)/(1+z*z))==0
    assert s.simplify(T.subs(z,1/t)-(theta-beta))==0
    assert s.simplify(T.diff(z)+z/s.sqrt(1+z*z))==0
    # Exact rational cutoff: asinh(12)-asinh(1)<log(12)<5/2,
    # sqrt(2)<3/2, hence theta12-T0<4<sqrt(17).
    assert sum((Q(5,2)**i/factorial(i) for i in range(7)),Q(0))>12
    assert Q(3,2)**2>2 and 4**2<17
    # z=4 is timelike, induced time metric strictly negative.
    assert s.simplify(gt[0,0].subs(z,4)+1/(16*(1+t*t)))==0
    print('15 grouped exact geometry and causal cutoff checks PASS')

if __name__=='__main__':run()
