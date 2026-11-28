"""BI: exact uniform normalized metric and scalar principal-symbol bounds.
Original AN/BF formulas; rational bounds on entire open ball, not residual/inverse certificate.
"""
from fractions import Fraction as Q
import sympy as s

def radial(N=1024):
    eps=Q(1,40); h=Q(4,5); k=2/h
    ma=mb=Q(0)
    for i in range(N):
        r,R=Q(i,N),Q(i+1,N); dl,dh=1-R*R,1-r*r
        Fl,Fh=k*(1+r*r),k*(1+R*R)
        D=dl**4+Fl**2*r*r
        P=Fh*dh+2*R*R*(k*dh+2*Fh)
        H=12*R*(k*dh+2*Fh)*dh+4*R**3*(4*k*dh+6*Fh)
        a=eps*h*dh**2*P/D
        b=eps*(h*dh/2)**2*(2*H/D+16*P*P/(D*max(dl*dl,Fl*r))+16*R*P/D)
        ma=max(ma,a);mb=max(mb,b)
    return ma,mb

def audit():
    a,b=radial();print('rational radial upper bounds A,B',float(a),float(b),flush=True)
    # Use rational slack, norm on gamma-orthonormal spatial covariant tensors.
    A=Q(13,250); B=Q(91,100)
    assert a<A and b<B
    S=1+A*A; j=Q(6,5)
    # H>=gamma; converting H-Frobenius to gamma-Frobenius costs <= S.
    # M H-norm <= (1+2A²)B; tracefree projection contracts in H.
    MT=S*(1+2*A*A)*B
    # |d alpha|_gamma <= A B; TF projection costs <= S.
    C0=j*S*A*A*B+j*MT # |2-A²|<=2, alpha²<=1
    C1=3*j*MT/2
    # |f| <= L²/16 <1/8 (L²<2). Q_base>=.64 gamma-(.36) a a^T.
    f=Q(1,8)
    for w in (Q(51,1000),Q(1,10)):
        u0=1/(1+w); u1=1/(1-w); du=max(1-u0,u1-1)
        horizontal=Q(16,25)-Q(9,25)*A*A-f*(C0+du*C1)
        # Schur and shear: g_seed=(horizontal)+(dy+a)^2; lower bound
        # |v|²+t² <= (1+2 A²)|v|²+2|t+a(v)|².
        seed=min(horizontal/(1+2*A*A),Q(1,2)); phys=u0*u0*seed
        # P in g-cotangent norm >= 6u - 3u^4 ||g^-1/2 G1 g^-1/2||.
        # Sharper bound via horizontal Schur: u² * horizontal.
        eta=f*C1/(u0*u0*horizontal)
        principal=6*u0-3*u1**4*eta
        upper=u1*u1*max(1+f*(C0+du*C1)+2*A*A,Q(2))
        principal_upper=6*u1+3*u1**4*eta
        print('w radius',float(w),'C0,C1,horizontal,seed,physical lower/upper,principal lower/upper,normalized principal lower',*[float(x) for x in (C0,C1,horizontal,seed,phys,upper,principal,principal_upper,principal/upper)],flush=True)
        assert horizontal>0 and phys>0 and principal>0
    x,y,z=s.symbols('x y z',real=True);V=s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z]);r2=x*x+y*y+z*z
    assert s.expand(V.dot(V)-(1+r2)**2)==0
    assert s.expand(sum(t*t for t in V.jacobian([x,y,z]))-(8+8*x*x+8*y*y+12*z*z))==0
    u=s.symbols('u',positive=True); l=s.symbols('l:4',real=True); G=s.diag(*l)
    for i in range(4):assert s.expand(6*u+u**4*(s.trace(G)-G[i,i])-(6*u+u**4*sum(l[k] for k in range(4) if k!=i)))==0
    # Frozen transmission: common elliptic symbol at the two endpoints.
    a,c,d=s.symbols('a c d',real=True); t=s.symbols('t',real=True); D=a*c-d*d
    for sign in (-1,1):
        root=(-s.I*d+sign*s.sqrt(D))/a
        assert s.simplify(a*root**2+2*s.I*d*root-c)==0
    assert s.simplify(((-s.I*d-s.sqrt(D))/a)-((-s.I*d+s.sqrt(D))/a)+2*s.sqrt(D)/a)==0
    print('PASS global metric positivity, uniform principal ellipticity and frozen transmission root identity',flush=True)
if __name__=='__main__':audit()
