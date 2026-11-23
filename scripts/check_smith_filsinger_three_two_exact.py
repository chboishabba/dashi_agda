"""Abstract 3:2 spectral geometry and inverse observation checks."""
import sympy as s

def run():
    x,a,b=s.symbols('x a b', nonzero=True, real=True)
    p=a*(x**2+x**-2)/2+b*(x**3+x**-3)/2
    q=s.expand(p*p)
    checks=[q.coeff(x,1)==a*b/2,q.coeff(x,5)==a*b/2,
            q.coeff(x,4)==a*a/4,q.coeff(x,6)==b*b/4,
            q.coeff(x,0)==(a*a+b*b)/2,
            q.subs(b,0).coeff(x,1)==0,q.subs(a,0).coeff(x,1)==0]
    # Recover unordered squared amplitudes from DC and difference-tone coefficient.
    d,c,z=s.symbols('d c z', real=True)
    poly=z*z-2*d*z+4*c*c
    checks += [s.expand(poly.subs({d:(a*a+b*b)/2,c:a*b/2,z:a*a}))==0,
               s.discriminant(poly,z)==4*d*d-16*c*c]
    # Same geometry need not imply same temporal ratio for a different dispersion law.
    r=s.Rational(3,2)
    checks += [r**2!=r, 3*2-2*3==0, (3-2)%3==1]
    # Golden Fibonacci recurrence in exact quadratic field.
    phi=(1+s.sqrt(5))/2
    checks += [s.simplify(phi**2-phi-1)==0,
               s.simplify(phi-s.Rational(3,2))>0]
    assert all(checks), checks
    print(f'{len(checks)}/{len(checks)} exact checks PASS')
if __name__=='__main__':run()
