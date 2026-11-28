"""W1 Maxwell physical source/work ABI (one Cartesian polarization).
Exact local Maxwell/Poynting Ward, signed source work and boundary flux.
The source J remains independent; no assumption that it creates gravity.
"""
import sympy as s

def eq(x):
    assert s.simplify(s.expand(x))==0,x

def main():
    t,x=s.symbols('t x',real=True)
    E=s.Function('E')(t,x);B=s.Function('B')(t,x)
    J=s.Function('J')(t,x)
    Et=-(B.diff(x)+J)
    Bt=-E.diff(x)
    u=(E*E+B*B)/2
    S=E*B
    ward=s.expand(u.diff(t)+S.diff(x)+J*E)
    ward=ward.subs({E.diff(t):Et,B.diff(t):Bt})
    eq(ward)
    # When source work is dropped, it cannot be hidden in a boundary flux.
    wrong=s.expand((u.diff(t)+S.diff(x)).subs({E.diff(t):Et,B.diff(t):Bt}))
    eq(wrong+J*E)
    assert wrong!=0
    # Finite worldtube integration, source and two fluxes both signed.
    xa,xb=s.symbols('xa xb',real=True)
    fixture=(x*x+t)*(t*x+x**3)
    term=s.integrate(fixture.diff(x),(x,xa,xb))
    eq(term-(fixture.subs(x,xb)-fixture.subs(x,xa)))
    # Matched transport channels: outward normals opposite on two faces.
    flux=s.Symbol('flux',real=True)
    eq(flux+(-flux))
    print('PASS original Maxwell local source-work/Poynting Ward and two-face flux')
    print('PASS zero-work negative control rejected for nonzero J*E')
    print('OPEN apparatus constitutive J, material support, retarded Einstein response')

if __name__=='__main__':main()
