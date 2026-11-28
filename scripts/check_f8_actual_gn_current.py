"""F8 GN 5D nonfrozen warped principal ADM current, a^3 spatial weight.
Specializes Hopf BR83 without claiming a coupled Einstein/Israel estimate.
"""
import sympy as s

def exact():
    a,N,p,q=s.symbols('a N p q',positive=True)
    at,an,Nt,Nn,pt,pn,qt,qn=s.symbols('at an Nt Nn pt pn qt qn',real=True)
    xs=(a,N,p,q)
    def deriv(expr,vals):return sum(s.diff(expr,x)*dx for x,dx in zip(xs,vals))
    dt=lambda x:deriv(x,(at,Nt,pt,qt))
    dn=lambda x:deriv(x,(an,Nn,pn,qn))
    E=(p**2/N**2+q**2)/2
    Jt=-a**3*E
    Jn=a**3*p*q
    wave=-dt(a**3*p/N)+dn(N*a**3*q)
    residual=s.factor((dt(Jt)+dn(Jn)-wave*p/N).subs(pn,qt))
    expected=3*a*a*at*(p**2/N**2-q**2)/2-a**3*Nn*p*q/N
    assert s.factor(residual-expected)==0,(residual,expected)
    # Independent BR83 stress/deformation computation for diag(-N²,a²,a²,a²,1).
    norm=-p**2/N**2+q**2
    Ttt=p**2/N**4+norm/(2*N**2)
    Tnn=q**2-norm/2
    Ttn=-p*q/N**2
    Ltt=s.S.Zero; Lsp=2*a*at/N; Ltn=Nn
    deform=s.factor(N*a**3*(Ttt*Ltt+2*Ttn*Ltn+3*(-norm/(2*a*a))*Lsp)/2)
    assert s.factor(residual-deform)==0
    # GN F8 wall metric a=t, N=1, a_t=1, N_n=-1/B.
    t=s.symbols('t',positive=True);B=s.sqrt(1+t**-2)
    wall={a:t,N:s.S.One,at:s.S.One,Nn:-1/B}
    assert s.simplify(residual.subs(wall)-3*t*t*(p*p-q*q)/2-t**3*p*q/B)==0
    # Wall energy and flux, and non-dissipative negative control.
    assert s.factor(Jt.subs(wall)+t**3*(p*p+q*q)/2)==0
    assert s.factor(Jn.subs(wall)-t**3*p*q)==0
    assert Jn.subs({a:1,p:1,q:1})>0 and Jn.subs({a:1,p:1,q:-1})<0
    # Off-shell mixed derivative defect is not projected away.
    defect=s.factor(dt(Jt)+dn(Jn)-wave*p/N-residual)
    assert s.simplify(defect-a**3*q*(pn-qt))==0
    print('PASS: F8 five-dimensional nonfrozen GN stress current, wall flux, mixed-jet defect')

if __name__=='__main__':exact()
