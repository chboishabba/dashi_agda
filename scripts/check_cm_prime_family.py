"""Odd prime self-isogeny examples: exact jets, conditional on classical CM values."""
from sympy import Poly, QQ, Rational, symbols, invert
from time import perf_counter
from check_cm163_modular_diagonal import diagonal
from check_cm163_derivative_slice import slice_poly
from check_cm163_fast import logder

def main():
    x=symbols('x')
    for p,K in [(3,-32768),(5,-884736),(11,-884736000),(17,-147197952000)]:
        t=perf_counter(); P=diagonal(p,logder); S=slice_poly(p,K,logder)
        assert P==diagonal(p) and S==slice_poly(p,K)
        P=P.shift(K);S=S.shift(K)
        assert P.nth(0)==P.nth(1)==S.nth(0)==S.nth(1)==0
        a,b=S.nth(2),S.nth(3); c=P.nth(2)-2*a; d=P.nth(3)/2-b
        m=Poly(p*x*x+(2*p-1)*x+p,x,domain=QQ)
        def red(v):return Poly(v,x,domain=QQ).rem(m)
        assert a and red(a*(1+x*x)+c*x).is_zero
        den=red((c+2*a*x)*(x*x-x));num=red(-2*(b*(1+x**3)+d*(x+x*x)))
        k=(num*invert(den,m)).rem(m);assert k.degree()<=0
        s=4+3*Rational(K,K-1728)-6*K*k.nth(0)
        print('PASS', 'D',1-4*p,'p',p,'K',K,'s2',s,'seconds',perf_counter()-t,flush=True)
if __name__=='__main__':main()
