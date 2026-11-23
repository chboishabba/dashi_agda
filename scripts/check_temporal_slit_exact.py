"""Ideal coherent aperture observation, not a calibrated scattering model."""
import sympy as s

def run():
    a,b,c,d=s.symbols('a b c d', real=True)
    u,v=a+s.I*b,c+s.I*d
    norm=lambda z:s.expand(z*s.conjugate(z))
    checks=[s.expand(norm(u+v)-norm(u)-norm(v)-2*(a*c+b*d))==0]
    phi=s.symbols('phi',real=True)
    checks.append(s.trigsimp(s.expand_complex(norm(1+s.exp(s.I*phi)))-2-2*s.cos(phi))==0)
    for phase,expected in [(1,4),(-1,0),(s.I,2),(-s.I,2)]:
        checks.append(norm(1+phase)==expected)
    w=(-1+s.I*s.sqrt(3))/2
    checks.append(s.simplify(1+w+w*w)==0)
    checks.append(s.simplify(norm(w)-1)==0)
    # Same intensity, opposite relative phase: inverse observation is ambiguous.
    checks.append(norm(1+s.I)==norm(1-s.I))
    assert all(checks),checks
    print(f'{len(checks)}/{len(checks)} PASS; SymPy {s.__version__}')
if __name__=='__main__':run()
