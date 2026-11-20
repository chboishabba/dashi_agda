"""Finite source duality and exact normalized Bessel differential bridge."""
import sympy as s

def check():
    u,k=s.symbols('u k', positive=True)
    f=s.Function('f')(u)
    D=lambda n:s.diff(f,u,n)
    forms=[s.Rational(2,5)*(D(4)+4*D(3)/u),s.Rational(4,7)*(D(4)+D(3)/u-6*D(2)/u**2+6*D(1)/u**3)/u**2,s.Rational(1,35)*(D(4)-6*D(3)/u+15*D(2)/u**2-15*D(1)/u**3)/u**4]
    for q,form in enumerate(forms):
        ell=2*q; d=3+2*ell
        phi=s.factorial2(2*ell+1)*s.expand_func(s.jn(ell,k*u))/(k*u)**ell
        assert s.simplify(s.diff(phi,u,2)+(d-1)/u*s.diff(phi,u)+k*k*phi)==0
        p=s.expand(u**(d-1)*form)
        adj=s.simplify(sum((-1)**n*s.diff(p.coeff(D(n))*phi,u,n) for n in range(1,5)))
        target=[s.Rational(2,5)*k**4,-s.Rational(60,7)*k**2,s.Integer(27)][q]*u**2*s.sin(k*u)/(k*u)
        assert s.simplify(s.trigsimp(adj-target))==0,(ell,adj)
        print('ell',ell,'exact Bessel source adjoint PASS',flush=True)
    # Non-nested weighted overlap Gram is not an identity (YM block floor
    # is not a radial Gram formula). Exact rational example, dimension 3.
    C=[(0,s.Rational(2,3)),(s.Rational(2,3),1)]
    F=[(0,s.Rational(1,2)),(s.Rational(1,2),1)]
    for d in (3,7,11):
        mass=lambda a,b:(b**d-a**d)/d
        Wc=s.diag(*[mass(*p) for p in C]); Wf=s.diag(*[mass(*p) for p in F])
        O=s.Matrix([[mass(max(a,c),min(b,e)) if min(b,e)>max(a,c) else 0 for c,e in C] for a,b in F])
        I=Wf.inv()*O; J=Wc.inv()*O.T
        assert Wc*J==I.T*Wf
        assert I*s.ones(2,1)==s.ones(2,1) and J*s.ones(2,1)==s.ones(2,1)
        E=Wc-I.T*Wf*I
        assert E==E.T and E.det()==0 and E[0,0]>0 and E[1,1]>0
        assert J*I!=s.eye(2)
        print('dimension',d,'weighted Gram defect PASS',flush=True)
if __name__=='__main__':check()
