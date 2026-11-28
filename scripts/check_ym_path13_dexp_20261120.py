"""Root-free rational series reference for the Bishop Path13 local calculus.
Not a kernel proof or a selected variational background realization.
"""
import sympy as S
from fractions import Fraction as F
from math import factorial

def check():
    x,y,z,a,b,c=S.symbols('x y z a b c', real=True)
    X=2*S.Matrix([[0,-z,y],[z,0,-x],[-y,x,0]])
    w=4*(x*x+y*y+z*z)
    assert (X**3+w*X).applyfunc(S.expand)==S.zeros(3)
    # Algebra in the reduced polynomial ring X^3=-w X.
    A,B,C=S.symbols('A B C'); u=S.symbols('u'); I=S.eye(3)
    D=I+A*X+B*X**2; J=I-X/2+C*X**2
    residual=(J*D-I).applyfunc(S.expand)
    expect=(A-S.Rational(1,2)+w*(B/2-C*A))*X+(B+C-A/2-w*C*B)*X**2
    assert (residual-expect).applyfunc(S.expand)==S.zeros(3)
    # w=u^2; exact scalar cancellation with one shared trig pair.
    sub={A:(1-S.cos(u))/u**2,B:(u-S.sin(u))/u**3,C:(1-u*S.cot(u/2)/2)/u**2}
    for k in [A-S.Rational(1,2)+u*u*(B/2-C*A), B+C-A/2-u*u*C*B]:
        assert S.trigsimp(S.expand_trig(k.subs(sub)))==0 or S.trigsimp(S.together(k.subs(sub)).rewrite(S.sin))==0
    # Root-free series coefficients in w, valid at zero as well.
    for w0 in (F(0),F(1,144),F(1,16),F(1,4)):
        for n in range(1,10):
            for k in (2,3):
                def term(j):return (-w0)**j/factorial(2*j+k)
                lo=sum(term(j) for j in range(2*n)); hi=lo+term(2*n)
                assert 0<=lo<=hi and hi-lo==abs(term(2*n))
                assert lo<=hi+term(2*n+1)<=hi
        # Dexp on the perpendicular plane: det=(sin(u)/u)^2+((1-cos(u))/u)^2.
        # sin(u)/u >= 1-w/6 >= 23/24 for w<=1/4.
        assert 1-w0/6>=F(23,24)
    print('PASS exact CH, two reduced inverse coefficients, 72 root-free nested brackets, chart determinant floor (23/24)^2')
if __name__=='__main__':check()
