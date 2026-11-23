"""Dimensionless observation discriminator, not a cavity excitation model."""
import sympy as s

def run():
    x=s.symbols('x', nonzero=True)
    a,b=s.symbols('a b', real=True)
    p=a*x+b/x
    q=s.expand(p*p)
    checks=[q.coeff(x,2)==a*a,q.coeff(x,-2)==b*b,q.coeff(x,0)==2*a*b]
    f=s.Rational(783,100)
    checks += [2*(f/2)==f,7800-1000*f==-30]
    assert all(checks)
    print(f'{len(checks)}/{len(checks)} PASS; SymPy {s.__version__}')
if __name__=='__main__':run()
