"""F8 primitive wall-memory energy and source contraction enclosure.
Original scalar reverse PDE; fixed positive memory metric. No TT/tail claim.
"""
import json
import sympy as S

def check():
    u,a,b,k,W,N,Y,j0,j1,g=S.symbols('u a b k W N Y j0 j1 g',real=True)
    s=1-u*u;w=b**-3;alpha=2*u/(1+u*u);eta=s/(1+u*u);d=a-3*u*u/b;c=3*u/(2*b)
    # m0=b^(3/2) J0, m1=b^(3/2) J1/k, p=sqrt(w0) W, F0=sqrt(w0) Y.
    m0,m1,p,F0,e,xi0,xi1=S.symbols('m0 m1 p F0 e xi0 xi1',real=True)
    F1=(u*(m0+e)-p)/(1+u*u)
    md0=c*m0-s*k*m1+d*F1+u*k*k*F0+xi0
    md1=c*m1+u*k*F1+xi1
    boundary=-alpha*p*p-eta*p*(m0+e)
    l0=eta+d/(1+u*u);l1=u*k/(1+u*u);ell=l0*m0+l1*m1
    c00=c+u*d/(1+u*u)+l0*l0/(2*alpha);c11=c+l1*l1/(2*alpha)
    c01=(-s*k+u*u*k/(1+u*u))/2+l0*l1/(2*alpha)
    # Algebraic equality before upper-bounding the two completed squares.
    prod=boundary+m0*md0+m1*md1
    rhs=-alpha*p*p/4+c00*m0*m0+2*c01*m0*m1+c11*m1*m1+u*k*k*m0*F0+m0*xi0+m1*xi1+u*e*(d*m0+u*k*m1)/(1+u*u)+eta*eta*e*e/alpha
    assert S.cancel(rhs-prod-alpha*(p+ell/alpha)**2/2-alpha*(p+2*eta*e/alpha)**2/4)==0
    # Verify scaled memory equations from literal reverse ODEs, source cancels in error.
    wroot=b**(-S.Rational(3,2));f1=-W+u*N
    M0=b**S.Rational(3,2)*j0;M1=b**S.Rational(3,2)*j1/k
    J0rhs=-s*j1+d*w*f1+u*k*k*w*Y;J1rhs=u*k*k*w*f1
    dt0=S.diff(M0,b)*u+S.diff(M0,j0)*J0rhs;dt1=S.diff(M1,b)*u+S.diff(M1,j1)*J1rhs
    assert S.simplify(dt0-(c*M0-s*k*M1+d*wroot*f1+u*k*k*wroot*Y))==0
    assert S.simplify(dt1-(c*M1+u*k*wroot*f1))==0
    assert S.cancel((u*(m0+e)-p)/(1+u*u)-(-W+u*N).subs({W:p,N:(u*p+m0+e)/(1+u*u)}))==0
    # Exact source contraction coefficients: - (w gsrc)' f1 - v gsrc J1.
    g0,gT=S.symbols('g0 gT');v=-u;h1=wroot*(gT-3*v*g0/b);h2=v*g0*k*wroot
    assert S.simplify(-h1*wroot*f1-h2*M1-(-(w*gT-3*v*w*g0/b)*f1-v*g0*j1))==0
    return dict(checks=5,sympy=S.__version__,scope='signed energy square completion, scaled memory and source coefficients; no bound inferred from samples')

if __name__=='__main__':print(json.dumps(check(),indent=2))
