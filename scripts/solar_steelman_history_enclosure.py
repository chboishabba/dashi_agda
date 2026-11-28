"""Sufficient history-return enclosure arithmetic.
All supplied bounds must be independently certified; floats are rejected.
No actual distributed stability result is asserted.
"""
import sympy as S

def rat(x):
    if isinstance(x,float) or isinstance(x,S.Float):raise TypeError("exact rational bounds required")
    q=S.Rational(x)
    if q<0:raise ValueError("nonnegative bound required")
    return q

def interpolation(lipschitz,spacing):
    return rat(lipschitz)*rat(spacing)/2

def power_error(norm,error,p):
    """Telescoping bound on ||T^p-A^p|| in one common operator norm."""
    a,e=map(rat,(norm,error))
    if not isinstance(p,int) or p<1:raise ValueError("positive integer power")
    return e*sum((a+e)**j*a**(p-1-j) for j in range(p))

def certificate(norm,error,p,power_norm):
    b=rat(power_norm)+power_error(norm,error,p)
    return dict(bound=b,contracting=bool(b<1),margin=1-b)

def history_error(initial_lipschitz,spacing,amplification,returned_lipschitz,integration_error):
    # For a common sup norm: input interpolation, propagation, output
    # interpolation, numerical integration. This is only a Lipschitz-class
    # estimate; not an operator norm on unrestricted continuous histories.
    return rat(amplification)*interpolation(initial_lipschitz,spacing)+interpolation(returned_lipschitz,spacing)+rat(integration_error)

def fixture():
    assert interpolation(2,S.Rational(1,10))==S.Rational(1,10)
    assert power_error(2,S.Rational(1,10),2)==S.Rational(41,100)
    assert certificate(2,S.Rational(1,100),2,S.Rational(1,2))['contracting']
    assert not certificate(2,S.Rational(1,10),2,S.Rational(9,10))['contracting']
    # A finite section cannot approximate identity uniformly on the entire
    # continuous unit ball: a triangular bump between knots is invisible.
    x=S.symbols('x',real=True);f=1-abs(2*x-1)
    assert f.subs(x,0)==f.subs(x,1)==0 and f.subs(x,S.Rational(1,2))==1
    print("PASS exact enclosure arithmetic fixtures; no actual return bounds supplied")

if __name__=="__main__":fixture()
