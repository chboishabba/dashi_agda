"""Original TOV/Schwarzschild moving-wall second-order geometric matching.
Necessary Cauchy data; does not assert bulk Einstein or GHY existence.
"""
import sympy as s

def zero(x):
    assert s.factor(s.cancel(x)) == 0, s.factor(x)

def main():
    r,l,e,phi,psi=s.symbols("r lambda eps phi psi",real=True)
    mass=l*(l+2)/15
    f=1-l*(l+2)*(r*r/3-r**4/5)
    ext=1-2*mass/r
    P=(l+2)*(s.Rational(1,3)-r*r/5)/2-(1-r*r)**2/2
    n=r*l*P/f
    ne=mass/(r*r*ext)
    moved=1+e*phi+e*e*psi/2
    for tag,internal,external in (("f",f,ext),("nu_prime",n,ne)):
        d=s.factor(internal-external)
        for k in (0,1):zero(s.diff(d,r,k).subs(r,1))
        d2=s.factor(s.diff(d,r,2).subs(r,1))
        d3=s.factor(s.diff(d,r,3).subs(r,1))
        assert d2!=0
        a=s.Function(tag+"_first_jump")(r)
        b=s.Function(tag+"_second_jump")(r)
        jet=d.subs(r,moved)+e*a.subs(r,moved)+e*e*b.subs(r,moved)/2
        zero(jet.diff(e).subs(e,0)-a.subs(r,1))
        zero(jet.diff(e,2).subs(e,0)-(b.subs(r,1)+2*phi*a.diff(r).subs(r,1)+phi*phi*d2))
        radial=s.diff(d,r).subs(r,moved)+e*a.diff(r).subs(r,moved)+e*e*b.diff(r).subs(r,moved)/2
        zero(radial.diff(e).subs(e,0)-a.diff(r).subs(r,1)-phi*d2)
        zero(radial.diff(e,2).subs(e,0)-(b.diff(r).subs(r,1)+2*phi*a.diff(r,2).subs(r,1)+phi*phi*d3+psi*d2))
        # First normal matching forces a'(1)=-phi d2; second value
        # matching then REQUIRES b(1)=+phi² d2 (not a bulk solution).
        required=s.factor((-2*phi*a.diff(r).subs(r,1)-phi*phi*d2).subs(a.diff(r).subs(r,1),-phi*d2))
        zero(required-phi*phi*d2)
        print(tag,"background D2 =",d2,"background D3 =",d3)
        print(tag,"necessary dynamic b(1) =",required)
        print(tag,"necessary dynamic b'(1) =",-2*phi*a.diff(r,2).subs(r,1)-phi*phi*d3-psi*d2)
    print("PASS exact moving second-order Cauchy-data inverse for both original channels")
    print("OPEN bulk Einstein material response, induced-metric embedding, GHY/corners")

if __name__=="__main__":main()
