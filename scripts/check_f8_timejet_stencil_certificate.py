"""F8 W1/W3 finite-history Ward time-jet certification socket.

Five-point central stencils are certified ONLY when the true source has
independently established C5/C6 uniform bounds on [t-2h,t+2h].
No inference from h/2 agreement to a derivative bound is permitted.
"""
import sympy as s
from fractions import Fraction as F

OFFSETS=(-2,-1,0,1,2)
FIRST=(1,-8,0,8,-1)
SECOND=(-1,16,-30,16,-1)


def exact():
    h=s.symbols('h',positive=True)
    # Exact finite moments: D1 polynomial order 4, D2 polynomial order 5.
    for degree in range(5):
        got=sum(c*(j*h)**degree for c,j in zip(FIRST,OFFSETS))/(12*h)
        want=1 if degree==1 else 0
        assert s.expand(got-want)==0,(degree,got)
    for degree in range(6):
        got=sum(c*(j*h)**degree for c,j in zip(SECOND,OFFSETS))/(12*h*h)
        want=2 if degree==2 else 0
        assert s.expand(got-want)==0,(degree,got)
    # Separate Taylor remainder for each sample, centered at t:
    # |f(t+jh)-T_m(t+jh)| <= sup |f^(m+1)| |jh|^(m+1)/(m+1)!
    # (The true uniform sup over the stencil's domain must be supplied.)
    e1=F(sum(abs(c)*abs(j)**5 for c,j in zip(FIRST,OFFSETS)),12*120)
    e2=F(sum(abs(c)*abs(j)**6 for c,j in zip(SECOND,OFFSETS)),12*720)
    assert e1==F(1,18) and e2==F(1,54)
    # These bounds are conservative; they don't depend on cancellation of
    # the unknown remainders across sample points.
    M5,M6=s.symbols('M5 M6',nonnegative=True)
    bound1=s.Rational(e1.numerator,e1.denominator)*h**4*M5
    bound2=s.Rational(e2.numerator,e2.denominator)*h**4*M6
    assert s.simplify(bound1.subs(h,h/2)-bound1/16)==0
    assert s.simplify(bound2.subs(h,h/2)-bound2/16)==0
    # The two observed stencils' disagreement can be bounded via the
    # triangle inequality, but it never upper-bounds the true error alone.
    assert s.simplify((bound1+bound1/16)-s.Rational(17,16)*bound1)==0
    assert s.simplify((bound2+bound2/16)-s.Rational(17,16)*bound2)==0
    print('PASS five-point Ward jet moment certificate: |D1-f_t|<=h^4 M5/18, |D2-f_tt|<=h^4 M6/54')


def certified(h,M5,M6):
    """Numeric error allowances; caller must prove bounds M5,M6 first."""
    if h<=0 or M5<0 or M6<0:raise ValueError('positive h and derivative bounds')
    return {'dt':h**4*M5/18,'dtt':h**4*M6/54}

if __name__=='__main__':exact()
