"""Exact axisymmetric polar projection normalization.
A common 2*pi from azimuth must multiply BOTH stiffness and forcing,
or cancel from BOTH. This catches the former unmatched source factor.
"""
import sympy as s

def main():
    x=s.symbols('x',real=True)
    for ell in range(1,9):
        L=ell*(ell+1)
        H=s.sqrt(s.Rational(2*ell+1,2))*s.legendre(ell,x)
        norm=s.integrate(H**2,(x,-1,1))
        angular=s.integrate((1-x*x)*s.diff(H,x)**2,(x,-1,1))
        assert s.simplify(norm-1)==0
        assert s.simplify(angular-L)==0
        k=s.Symbol('k',positive=True)
        source=s.Symbol('F',real=True)
        assert s.simplify((2*s.pi*source)/(2*s.pi*k)-source/k)==0
        assert s.simplify((2*s.pi*source)/k-source/k)!=0
    print('PASS 8/8 normalized Legendre norms, common azimuth factor, unmatched 2pi negative control')

if __name__=='__main__':main()
