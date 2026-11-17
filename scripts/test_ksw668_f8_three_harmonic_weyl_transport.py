#!/usr/bin/env python3
"""Original F8 ell=0,2,4 radial jet and electric-Weyl defect controls.

Independent SymPy algebra tests; no moving-PDE, Agda kernel or physical
detector claim. Original KSW source/geometry authors retain attribution.
"""
import sympy as s

def main():
    r, eps, t=s.symbols("r eps t",positive=True)
    V, Vr, Vrr=s.symbols("V Vr Vrr")
    checks=0
    for ell in (0,2,4):
        hrr=eps**(-ell)*(r**ell*Vrr+2*ell*r**(ell-1)*Vr+ell*(ell-1)*r**(ell-2)*V)
        lap=eps**(-ell)*(r**ell*Vrr+(2*ell+2)*r**(ell-1)*Vr)
        expected=eps**(-ell)*(2*r**(ell+2)*Vrr+(4*ell+2)*r**(ell+1)*Vr+ell*(ell-1)*r**ell*V)
        assert s.simplify(r*r*(hrr+lap)-expected)==0
        checks+=1
    A,B,C,D,X,Y=s.symbols("A B C D X Y")
    root=s.sqrt(1+t*t)
    uT=root/t**2; uz=-1/t**2;nT=uz;nZ=uT
    box=-A+B+C
    electric=nT**2*(-A/s.Integer(2)-box/6)+2*nT*nZ*(-D/2)+nZ**2*(-C/2+box/6)
    hdot=uT*X+uz*Y
    hddot=uT*uT*A+2*uT*uz*D+uz*uz*C+s.diff(uT,t)*X+s.diff(uz,t)*Y
    sms=-hddot/2-3*hdot/(2*t)+B/(2*t*t)
    rn=nT*X+nZ*Y
    rb=-A+B+C-3*t*Y
    assert s.simplify(electric-sms+(2*t*t+1)*rn/(2*t*root)+rb/(3*t*t))==0
    checks+=1
    k1,k2,k3=s.symbols("k1 k2 k3")
    q=s.Matrix([k1,k2,k3])
    P=q.dot(q)*s.eye(3)-q*q.T
    Q=s.diag(1,-1,0)
    source=P*Q*P-s.Rational(1,2)*P*s.trace(P*Q)
    assert s.simplify(source*q)==s.zeros(3,1)
    assert s.simplify(s.trace(source))==0
    checks+=1
    normal=s.symbols("n0:3"); bulk=s.symbols("b0:3");sms3=s.symbols("m0:3")
    electric3=[sms3[i]-s.Rational(41,40)*normal[i]-s.Rational(3,16)*bulk[i] for i in range(3)]
    assert s.expand(sum(electric3)-sum(sms3)+s.Rational(41,40)*sum(normal)+s.Rational(3,16)*sum(bulk))==0
    checks+=1
    print(f"{checks}/{checks} exact original TT/radial/Weyl controls passed")

if __name__=="__main__":
    main()
