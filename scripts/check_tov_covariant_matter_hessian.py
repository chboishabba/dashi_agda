"""All-parity local covariant matter Hessian for original repaired TOV action.

Exact second jet in arbitrary metric/material directions. Metric h is a
covariant perturbation, A=dY, Z=d(delta Y). K1,K2,V1,V2 are directional
target derivatives, NOT independent physical fields. Local interior
identity only: Einstein curvature Hessian, gauge and constraints,
moving-domain terms and radiative matching still required.
"""
import sympy as s

def tr(M): return s.trace(M)
def eq(M): return M.applyfunc(s.expand)==s.zeros(*M.shape)

def jets(ginv,h,A,Z):
    B=A*ginv*A.T
    B1=Z*ginv*A.T+A*ginv*Z.T-A*ginv*h*ginv*A.T
    B2=2*(Z*ginv*Z.T-Z*ginv*h*ginv*A.T-A*ginv*h*ginv*Z.T
          +A*ginv*h*ginv*h*ginv*A.T)
    H=ginv*h
    return B,B1,B2,tr(H)/2,tr(H)**2/4-tr(H*H)/2

def matter(ginv,h,A,Z,K,K1,K2,V,V1,V2,B01,c):
    B,B1,B2,j1,j2=jets(ginv,h,A,Z)
    W=tr(K*B)+V
    W1=tr(K1*B+K*B1)+V1
    W2=tr(K2*B+2*K1*B1+K*B2)+V2
    D=B1-B01
    # B0=B on original background; cyclic traces avoid matrix square root.
    C=B.inv()*D
    W2+=c*(tr(C)**2-tr(C*C))
    return W2+2*j1*W1+j2*W

def main():
    e=s.symbols('e')
    gi=s.diag(-s.Rational(2,3),s.Rational(3,4),1,1)
    A=s.Matrix([[0,1,0,0],[0,0,1,0],[0,0,0,1]])
    B=A*gi*A.T
    K=s.diag(2,3,4); K1=s.Matrix([[1,2,0],[2,-1,1],[0,1,3]])/7
    K2=s.diag(1,-2,3)/11
    V,V1,V2,c=map(s.Rational,('2/7','-3/7','5/13','1/5'))
    # Exact independent polynomial oracle via inverse/determinant jets,
    # with polar, axial and mixed covariant metric perturbations.
    for seed in range(1,5):
        h=s.Matrix(4,4,lambda i,j:s.Rational(((min(i,j)+1)*(max(i,j)+2)+seed)%11-5,13))
        Z=s.Matrix(3,4,lambda i,j:s.Rational(((i+2)*(j+3)+seed)%13-6,17))
        B01=s.Matrix(3,3,lambda i,j:s.Rational((i+j+seed)%7-3,19))
        g=gi.inv(); J=g+e*h
        # Differentiate true inverse at e=0 independently.
        Jinv=J.inv()
        Aeps=A+e*Z
        Be=Aeps*Jinv*Aeps.T
        _,B1,B2,j1,j2=jets(gi,h,A,Z)
        assert eq(Be.diff(e).subs(e,0)-B1)
        assert eq(Be.diff(e,2).subs(e,0)-B2)
        det=s.det(J)/s.det(g)
        assert s.simplify(s.diff(s.sqrt(det),e).subs(e,0)-j1)==0
        assert s.simplify(s.diff(s.sqrt(det),e,2).subs(e,0)-j2)==0
        # Independent quadratic polynomial assembly after verified jets.
        bp=B+e*B1+e**2*B2/2
        kp=K+e*K1+e**2*K2/2
        C=B.inv()*(B1-B01)
        poly=(1+e*j1+e**2*j2/2)*(tr(kp*bp)+V+e*V1+e**2*V2/2
              +e**2*c*(tr(C)**2-tr(C*C))/2)
        assert s.expand(poly).coeff(e,2)*2==matter(gi,h,A,Z,K,K1,K2,V,V1,V2,B01,c)
    # Physical target jets from the original TOV source, including
    # direction changes of radial projector for tangential displacement.
    x,l=s.symbols('x l',positive=True); p=l/(8*s.pi)
    rho=(2+l)*p*(1-x); pr=-p*(1-x)**2
    f=1-l*(2+l)*(x/3-x*x/5); P=(2+l)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
    pt=s.factor(pr+x*s.diff(pr,x)+x*l*(rho+pr)*P/(2*f))
    a=(rho+pt)/2; d=(rho+pr)/(2*f); V=rho-2*a-d*f
    r=s.symbols('r',positive=True); u,v,w=s.symbols('u v w',real=True)
    Y=s.Matrix([r,0,0]); Z=s.Matrix([u,v,w]); I=s.eye(3)
    # P_r'= (Z_t n^T+n Z_t^T)/r.
    n=Y/r; T=Z-u*n
    P1=(T*n.T+n*T.T)/r
    # dB0/dY = f_s 2ru P_r + (f-1) P_r'.
    B01=2*r*u*s.diff(f,x).subs(x,r*r)*n*n.T+(f.subs(x,r*r)-1)*P1
    # Tangential target variations cannot be dropped in nonspherical Hessian.
    assert s.cancel(B01[0,1]-(f.subs(x,r*r)-1)*v/r)==0
    assert s.cancel(B01[0,2]-(f.subs(x,r*r)-1)*w/r)==0
    assert s.cancel(B01[0,0]-2*r*u*s.diff(f,x).subs(x,r*r))==0
    assert B01.subs(v,1).subs(w,0)[0,1]!=0
    # Second target derivatives for any scalar F(s) and K=aI+bYY^T.
    F,F1,F2,b,b1,b2,a0,a1,a2=s.symbols('F F1 F2 b b1 b2 a0 a1 a2')
    ds=2*Y.dot(Z); dds=2*Z.dot(Z)
    YY=Y*Y.T; YY1=Z*Y.T+Y*Z.T
    Yeps=Y+e*Z; ds_poly=e*ds+e**2*dds/2
    Ke=(a0+a1*ds_poly+a2*ds_poly**2/2)*I+(b+b1*ds_poly+b2*ds_poly**2/2)*Yeps*Yeps.T
    K2=(a2*ds**2+a1*dds)*I+(b2*ds**2+b1*dds)*YY+2*b1*ds*YY1+2*b*Z*Z.T
    assert eq(Ke.diff(e,2).subs(e,0)-K2)
    print('PASS arbitrary covariant metric/material second jets, volume, constitutive Hessian and target projector transport')
    print('OPEN Einstein-Hilbert bulk/boundary Hessian, harmonic constraints, physical polar and radiative stability')

if __name__=='__main__':main()
