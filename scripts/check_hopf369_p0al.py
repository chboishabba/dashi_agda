"""P0AL: exact AdS dimensional reduction discriminators and Hopf seam barriers.
Classical identities only; no Monster duality, numerical PDE or kernel claim.
"""
import sympy as s


def audit():
    c,h,L,z,y,k,T,d=s.symbols('c h L z y k T d',positive=True)
    b=s.cosh(c*(y-L/2))/s.cosh(c*L/2)
    h0=c/s.cosh(c*L/2)
    # AdS4 as AdS3-sliced warped product: both sectional curvatures -h^2.
    f=s.cosh(h*z)
    assert s.simplify(-s.diff(f,z,2)/f+h*h)==0
    assert s.trigsimp((-h*h-s.diff(f,z)**2)/f**2+h*h)==0
    # EH coefficient for ds5^2=dy^2+b^2(dz^2+f^2 ds3^2).
    Iy=(L/2+s.sinh(c*L)/(2*c))/s.cosh(c*L/2)**2
    primitive=y/2+s.sinh(2*c*(y-L/2))/(4*c)
    assert s.trigsimp(s.diff(primitive,y)-s.cosh(c*(y-L/2))**2)==0
    assert s.simplify((primitive.subs(y,L)-primitive.subs(y,0))/s.cosh(c*L/2)**2-Iy)==0
    Z=s.symbols('Z',positive=True)
    Iz=s.integrate(f,(z,-Z,Z)); assert s.simplify(Iz-2*s.sinh(h*Z)/h)==0
    # Alternative Einstein product AdS3 x compact hyperbolic surface.
    genus,G5=s.symbols('genus G5',positive=True)
    K3=-2*c*c; K2=-4*c*c
    assert 2*K3==K2==-4*c*c
    area=s.pi*(genus-1)/c**2
    ell=1/(s.sqrt(2)*c); G3=G5/area
    bh=3*ell/(2*G3)
    assert s.simplify(bh.subs(G5,s.pi*(genus-1)/(16*s.sqrt(2)*c**3))-24)==0
    rm2=2*3*2*K3**2+2*2*K2**2
    assert s.expand(rm2-112*c**4)==0
    assert s.expand(rm2-2*5*4*c**4-72*c**4)==0
    # Product wall along a curve in the internal surface: no AdS3 jump.
    j=s.symbols('j',real=True); J=s.diag(0,0,0,j)
    S=-(J-s.trace(J)*s.eye(4))/k
    assert S==s.diag(j/k,j/k,j/k,0)
    # Exact surface residual for lower/upper nonlinear conformal barriers.
    # b=1 at seam and [b']=-kT/3. Boundary F=-[u_n]+kT(u-u^2)/3.
    ulo=1-d; uhi=1+d-2*d*d
    lower=s.expand(-d*k*T/3+k*T*(ulo-ulo**2)/3)
    upper=s.factor(d*k*T/3+k*T*(uhi-uhi**2)/3)
    assert lower==-k*T*d*d/3
    assert s.expand(upper-k*T*d*d*(1+4*d-4*d*d)/3)==0
    # Full isotropic jump after nonlinear conformal deformation.
    u=s.symbols("u",positive=True)
    ju=k*T*(u-u*u)/3
    assert s.simplify((-k*T/3+ju/u)/u+k*T/3)==0
    # Bulk background ground state and first variation of the constraint.
    lapb=s.diff(b,y,2)+3*s.diff(b,y)**2/b
    assert s.simplify(-lapb+4*c*c*b-3*h0*h0/b)==0
    # Original Hopf connection and helicity on the full noncompact base.
    x1,x2,x3,e=s.symbols('x1 x2 x3 e',real=True)
    x=s.Matrix([x1,x2,x3]); r2=x.dot(x); den=1+r2
    A=2*s.Matrix([2*x1*x3-2*x2,2*x1+2*x2*x3,1-x1*x1-x2*x2+x3*x3])/den**2
    B=s.Matrix([s.diff(A[2],x2)-s.diff(A[1],x3),s.diff(A[0],x3)-s.diff(A[2],x1),s.diff(A[1],x1)-s.diff(A[0],x2)])
    assert s.cancel(A.dot(B)-16/den**3)==0
    r=s.symbols('r',positive=True)
    assert s.integrate(4*s.pi*r*r*16/(1+r*r)**3,(r,0,s.oo))==4*s.pi**2
    chi=s.Function('chi')(y)
    # horizontal lift of theta=dy+e chi A: Frobenius obstruction
    # F_h = e chi dA (the chi' A wedge A contribution is zero).
    H=s.Matrix(3,3,lambda i,j:s.diff(A[j],x[i])-s.diff(A[i],x[j]))
    v=e*chi*A
    C=s.Matrix(3,3,lambda i,j:s.diff(v[j],x[i])-s.diff(v[i],x[j])-v[i]*s.diff(v[j],y)+v[j]*s.diff(v[i],y))
    assert (C-e*chi*H).applyfunc(s.expand)==s.zeros(3)
    print('PASS AdS3 slice curvature, EH weight, product Einstein and c=24 parameter, Weyl and wall discriminator, nonlinear surface barriers, Hopf helicity and horizontal curvature')

if __name__=='__main__': audit()
