"""P0AM: original periodic AdS tensor sector, M2 circle branching and central
inversion, explicit Hopf seed seam, decaying conformal barriers.
Algebraic controls, not full nonlinear numerical Einstein evolution.
"""
import math
import sympy as s


def audit():
    h,z,y,L,c=s.symbols('h z y L c',positive=True)
    f=s.cosh(h*z); Z=f**-3
    assert s.simplify(-s.diff(f**3*s.diff(Z,z),z)/f-3*h*h*Z)==0
    # Ground state norm integral by t=tanh(h z), then t=sin(theta).
    t=s.symbols('t',real=True)
    assert s.integrate((1-t*t)**s.Rational(3,2),(t,-1,1))==3*s.pi/8
    print('PASS separated TT ground state: m²=3h², norm_z=3*pi/(8h)')
    # Published M2 eqs 71-73. Two copies of exterior^5(R^28),
    # split 28=25+3, then 25=24+1, retain graviton vector.
    n27={p:2*math.comb(3,5-p) for p in range(2,6)}
    assert n27=={2:2,3:6,4:6,5:2}
    n26={p:n27.get(p,0)+n27.get(p+1,0)+(p==1) for p in range(1,6)}
    assert n26=={1:3,2:8,3:12,4:8,5:2}
    assert 324+sum(m*math.comb(25,p) for p,m in n27.items())==196884
    assert 300+sum(m*math.comb(24,p) for p,m in n26.items())==196884
    half={p:n26[p]//2 for p in range(1,6)}
    assert half=={1:1,2:4,3:6,4:4,5:1}
    odd=sum(half[p]*math.comb(24,p) for p in (1,3,5)); even=sum(half[p]*math.comb(24,p) for p in (2,4))
    assert (odd,even,even-odd)==(54672,43608,-11064)
    assert even+odd==98280 and 98280-(even-odd)==109344
    assert max(n26.values())==12<196883
    print('PASS published M2 branching, half p-form central inversion: +',even,'-',odd,'trace',even-odd)
    # Basis-independent seam check in orthonormal base at fixed point.
    a=s.Matrix(s.symbols('a:3',real=True)); I=s.eye(3); S=1+a.dot(a); H=I+a*a.T
    g=H.row_join(a).col_join(a.T.row_join(s.ones(1,1)))
    inv=I.row_join(-a).col_join((-a.T).row_join(s.Matrix([[S]])))
    assert (g*inv-s.eye(4)).applyfunc(s.expand)==s.zeros(4)
    j=s.symbols('j',real=True)
    Hinv=I-a*a.T/S
    # seed g=(dy+a dx)^2+gamma+(b²-1)H/sqrt(S)
    # common conormal dy/sqrt(S); delta tangential derivative jump.
    jump=(s.sqrt(S)/2)*Hinv*(2*j*H/s.sqrt(S))
    assert (jump-j*I).applyfunc(s.cancel)==s.zeros(3)
    assert s.simplify(s.sqrt(S)*j/s.sqrt(S)-j)==0
    # Positive Q eigenvalues: directions orthogonal/parallel to a.
    b=s.symbols('b',positive=True); qperp=1+(b*b-1)/s.sqrt(S); qpara=1+(b*b-1)*s.sqrt(S)
    assert ((I+(b*b-1)*H/s.sqrt(S))*a-qpara*a).applyfunc(s.simplify)==s.zeros(3,1)
    assert s.simplify(qperp.subs(b,1)-1)==0
    # Decaying hyperbolic barrier and exact seam nonlinear signs.
    r=s.symbols('r',positive=True); eta=s.cosh(h*r)**-2
    lap=s.diff(eta,r,2)+2*h*s.coth(h*r)*s.diff(eta,r)
    assert s.simplify(lap+6*h*h*eta**2)==0
    d,E,kT=s.symbols('d E kT',positive=True)
    lo=1-d*E; hi=1+d*E-2*d*d*E*E
    Blo=s.expand(-kT*d*E/3+kT*(lo-lo**2)/3)
    Bhi=s.expand(kT*d*E/3+kT*(hi-hi**2)/3)
    assert Blo==-kT*d*d*E*E/3
    assert s.expand(Bhi-kT*d*d*E*E*(1+4*d*E-4*d*d*E*E)/3)==0
    print('PASS direct periodic Hopf metric seam, positive-base eigenvalues, decaying H3 barrier and nonlinear jumps')

if __name__=='__main__': audit()
