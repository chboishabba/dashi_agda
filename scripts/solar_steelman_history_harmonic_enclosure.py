"""Rational Taylor/reciprocal enclosure primitives for harmonic slabs.
Polynomial plus uniform scalar error, on s in [0,1].
No floating coefficients or sampled extrema are accepted.
"""
import sympy as S
from solar_steelman_history_polynomial_defect import bernstein_bound

s=S.Symbol('s',real=True)
def rat(v):
    if isinstance(v,(float,S.Float)):raise TypeError('exact rational required')
    return S.Rational(v)
def norm(p):
    return bernstein_bound(S.Matrix([[p]]),s)
class Ball:
    def __init__(self,p,e=0):
        self.p=S.Poly(p,s,domain=S.QQ).as_expr()
        self.e=rat(e)
        assert self.e>=0
    def __add__(self,o):
        if not isinstance(o,Ball):o=Ball(o)
        return Ball(self.p+o.p,self.e+o.e)
    __radd__=__add__
    def __neg__(self):return Ball(-self.p,self.e)
    def __sub__(self,o):return self+-o
    def __mul__(self,o):
        if not isinstance(o,Ball):o=Ball(o)
        return Ball(self.p*o.p,norm(self.p)*o.e+norm(o.p)*self.e+self.e*o.e)
    __rmul__=__mul__
    def truncate(self,n):
        p=S.Poly(self.p,s);q=sum(p.nth(i)*s**i for i in range(n+1))
        return Ball(q,self.e+norm(self.p-q))
    def inverse(self,lower,degree=4):
        # lower is an independently proved positive lower bound on the TRUE
        # denominator. Approximate reciprocal by geometric polynomial.
        lower=rat(lower);assert lower>0
        a=rat(self.p.subs(s,0));assert a>0
        v=Ball(1)-self*Ball(1/a)
        q=Ball(0);term=Ball(1)
        # Use only approximate polynomial for q; certify actual residual
        # directly, avoiding unnecessary repeated uncertainty expansion.
        for i in range(degree+1):
            q=Ball(q.p+term.p)
            term=Ball(term.p*v.p)
        q=Ball(q.p/a)
        residual=Ball(1)-self*q
        return Ball(q.p,(norm(residual.p)+residual.e)/lower)

def trig(lo,hi,w,degree=32):
    """Global Taylor at zero, exact remainder via derivative <=1.
    Can be pessimistic near end of period; increase degree or use
    local addition formulas with certified centre values.
    """
    lo,hi,w=map(rat,(lo,hi,w));assert lo<=hi and degree>=0
    t=w*(lo+(hi-lo)*s);r=max(abs(w*lo),abs(w*hi))
    e=r**(degree+1)/S.factorial(degree+1)
    c=sum((-1)**(k//2)*t**k/S.factorial(k) for k in range(0,degree+1,2))
    z=sum((-1)**((k-1)//2)*t**k/S.factorial(k) for k in range(1,degree+1,2))
    return Ball(c,e),Ball(z,e)

def harmonic(c,lo,hi,degree=32,derivative=0):
    # c[-k]=conjugate(c[k]), exact rational complex Fourier coefficients.
    assert all(S.expand(c[-k]-S.conjugate(c[k]))==0 for k in range(1,5))
    out=Ball(c[0] if derivative==0 else 0)
    for k in range(1,5):
        v=S.expand((S.I*k)**derivative*c[k]);C,Z=trig(lo,hi,k,degree)
        out=out+2*(S.re(v)*C-S.im(v)*Z)
    return out

def ratios(c,lo,hi,degree=32,reciprocal_degree=4):
    from solar_steelman_history_exact_bounds import ratio_bounds
    lower,_,_=ratio_bounds(c)
    store=harmonic(c,lo,hi,degree)
    derivative=harmonic(c,lo,hi,degree,1)
    inv=store.inverse(lower,reciprocal_degree)
    return inv,derivative*inv

def fixture():
    a=Ball(2+s);b=a.inverse(2,4)
    assert b.e==S.Rational(1,64)
    C,Z=trig(0,1,1,3)
    assert C.p==1-s*s/2 and Z.p==s-s**3/6 and C.e==S.Rational(1,24)
    assert (Ball(s,S.Rational(1,10))*Ball(2,S.Rational(1,10))).e==S.Rational(31,100)
    print('PASS exact harmonic enclosure primitives')
if __name__=='__main__':fixture()
