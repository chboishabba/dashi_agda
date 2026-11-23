"""Abstract passive transfer ceilings, not a physical environmental excitation design."""
import sympy as s

def run():
    e,l,r,d=s.symbols('e l r d', positive=True)
    den=(e+l+r)**2+d**2
    eta=4*e*l/den
    checks=[s.cancel(1-eta-((e-l)**2+2*r*(e+l)+r*r+d*d)/den)==0,
            s.cancel(e/(e+r)-eta-e*((l-e-r)**2+d*d)/((e+r)*den))==0]
    a,b,c=s.symbols('a b c', nonnegative=True)
    checks += [s.expand(1-a*b*c-((1-a)+a*(1-b)+a*b*(1-c)))==0]
    # Arbitrary measured contraction; lossless transmission alone is insufficient
    # if the selected input has a component outside its transmitted subspace.
    T=s.diag(1,s.Rational(1,2),0)
    Q=s.eye(3)-T.H*T
    checks += [Q==s.diag(0,s.Rational(3,4),1), Q.nullspace()==[s.Matrix([1,0,0])]]
    x=s.Matrix(s.symbols('x:3', real=True))
    checks += [s.expand((x.T*x-(T*x).T*(T*x)-x.T*Q*x)[0])==0]
    assert all(checks)
    print(f'{len(checks)}/{len(checks)} exact checks PASS; SymPy {s.__version__}')
if __name__=='__main__':run()
