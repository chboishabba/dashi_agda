"""Original TOV spherical Einstein mass constraint pays moving Israel f-jets.
Necessary source parity, not nonlinear Einstein free-boundary existence.
"""
import sympy as s
def z(x):
    assert s.factor(s.cancel(x))==0,s.factor(x)
def main():
    r,l,e,phi,psi=s.symbols("r lambda eps phi psi",real=True)
    p=l/(8*s.pi);rho=(l+2)*p*(1-r*r)
    m=l*(l+2)*(r**3/s.Integer(3)-r**5/s.Integer(5))/2
    M=l*(l+2)/15
    z(s.diff(m,r)-4*s.pi*r*r*rho)
    Dm=m-M
    z(Dm.subs(r,1));z(s.diff(Dm,r).subs(r,1))
    M2=s.factor(s.diff(Dm,r,2).subs(r,1))
    assert M2==-l*(l+2)
    z(s.diff(1-2*m/r-(1-2*M/r),r,2).subs(r,1)+2*M2)
    rho1=s.Function("rho1")(r);rho2=s.Function("rho2")(r)
    m1=s.Function("m1")(r);m2=s.Function("m2")(r)
    R=1+e*phi+e*e*psi/2
    movedrho=rho.subs(r,R)+e*rho1.subs(r,R)+e*e*rho2.subs(r,R)/2
    eq1=s.factor(movedrho.diff(e).subs(e,0))
    eq2=s.factor(movedrho.diff(e,2).subs(e,0))
    z(eq1-rho1.subs(r,1)-phi*s.diff(rho,r).subs(r,1))
    z(eq2-rho2.subs(r,1)-2*phi*rho1.diff(r).subs(r,1)-phi*phi*s.diff(rho,r,2).subs(r,1)-psi*s.diff(rho,r).subs(r,1))
    rho1value=-phi*s.diff(rho,r).subs(r,1)
    z(rho1value-(l+2)*l*phi/(4*s.pi))
    mm=m+e*m1+e*e*m2/2
    rh=rho+e*rho1+e*e*rho2/2
    eq=s.expand(s.diff(mm,r)-4*s.pi*r*r*rh)
    for k,field in ((1,m1),(2,m2)):
        z(eq.diff(e,k).subs(e,0)-s.diff(field,r)+4*s.pi*r*r*(rho1 if k==1 else rho2))
    m1prime=(4*s.pi*r*r*rho1).subs(r,1).subs(rho1.subs(r,1),rho1value)
    z(m1prime+phi*M2)
    jumped=Dm.subs(r,R)+e*m1.subs(r,R)+e*e*m2.subs(r,R)/2
    z(jumped.diff(e).subs(e,0)-m1.subs(r,1))
    second=s.factor(jumped.diff(e,2).subs(e,0))
    z(second-m2.subs(r,1)-2*phi*m1.diff(r).subs(r,1)-phi*phi*M2)
    required=s.factor((-2*phi*m1.diff(r).subs(r,1)-phi*phi*M2).subs(m1.diff(r).subs(r,1),-phi*M2))
    z(required-phi*phi*M2)
    z(-2*required-2*l*(l+2)*phi**2)
    rho2required=-2*phi*rho1.diff(r).subs(r,1)-phi*phi*s.diff(rho,r,2).subs(r,1)-psi*s.diff(rho,r).subs(r,1)
    z((rho2.subs(r,1)-rho2required).subs(rho2.subs(r,1),rho2required))
    print("PASS TOV radial Einstein mass constraint, moving material source, second metric jet")
    print("rho1(1) =",rho1value,"m1'(1) =",s.factor(m1prime),"m2(1) =",required)
    print("f second correction =",s.factor(-2*required),"rho2(1) required =",rho2required)
    print("OPEN radial evolution, lapse Einstein equation, nonspherical source, EH GHY/corners")
if __name__=="__main__":main()
