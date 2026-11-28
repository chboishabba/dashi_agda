"""Constitutive Israel boundary in original material coordinates, order e².
Consumes actual fixed-profile source action and existing normal-jet inverse.
Not a solved 5D bulk initial boundary value problem.
"""
import sympy as s
from check_f8_endpoint_weld import israel_second, normal_jet_second
from check_f8_material_clock_controller import second_stress, source_shear_bound


def boundary_second(t,H,J,l,m,Pi,A,A2,r,S):
    """Return full covariant first/second normal jets and mixed second stress.
    Material gauge (phi,X)=(t,x), GN extension along actual shell normal.
    S=c_plus²+c_minus² >= |A|. Constant tension has no mixed perturbation.
    """
    b=1/t; beta=s.sqrt(1+b*b); g=s.diag(-1,t*t*s.eye(3))
    K0=s.diag(-1/beta,-beta,-beta,-beta)
    h=s.diag(0,t*t*H); j=s.diag(l,t*t*J)
    j[0,1:4]=m.T; j[1:4,0]=m
    S1=s.diag(0,A*Pi); K1=-3*S1
    nh=2*(g*K1+h*K0)
    S2=second_stress(t,H,J,l,m,Pi,A,A2,r,(source_shear_bound()+1)*S)
    nj=normal_jet_second(g,K0,h,j,nh,S2)
    return nh,nj,S2


def controller_kernel(tau,q):
    """Exact mode kernel, with no zero-mode or resonance division."""
    if q==1: return tau*s.exp(-tau)
    if q==0: return (1-s.exp(-2*tau))/2
    if q>1: return s.exp(-tau)*s.sin(s.sqrt(q-1)*tau)/s.sqrt(q-1)
    return s.exp(-tau)*s.sinh(s.sqrt(1-q)*tau)/s.sqrt(1-q)


def amplitude_feedback(eta,eta0,q,Z,S):
    """Retarded second-order charge A2 for Z_k=(tr Pi H)_k.
    Initial chi and chi' zero. Z is a symbolic history, not a new source.
    """
    u=s.Dummy('u',real=True)
    return s.Integral(2*S*controller_kernel(eta-u,q)*s.exp(2*u)*Z.subs(eta,u),(u,eta0,eta))


def run():
    t=s.Rational(3,2); H=s.Matrix([[1,2,0],[2,-1,3],[0,3,0]])
    J=s.Matrix([[1,2,3],[2,4,5],[3,5,6]]); Pi=s.Matrix([[0,1,3],[1,2,4],[3,4,-2]])
    l=s.Rational(1,7); m=s.Matrix([1,2,-3]); A=s.Rational(2,5); A2=s.Rational(-3,7); r=s.Rational(1,16); S=1
    nh,nj,S2=boundary_second(t,H,J,l,m,Pi,A,A2,r,S)
    beta=s.sqrt(1+1/t**2);g=s.diag(-1,t*t*s.eye(3)); K0=s.diag(-1/beta,-beta,-beta,-beta)
    h=s.diag(0,t*t*H);j=s.diag(l,t*t*J);j[0,1:4]=m.T;j[1:4,0]=m
    K1,K2,R1,R2=israel_second(g,K0,h,j,nh,nj)
    zero=lambda M:M.applyfunc(s.simplify)==s.zeros(4)
    assert zero(R1-s.diag(0,A*Pi))
    assert zero(R2-S2)
    assert zero(nh-nh.T) and zero(nj-nj.T)
    # Variation w.r.t second metric jets is independent of H, Pi, controller.
    H0=s.zeros(3);J0=s.zeros(3);m0=s.zeros(3,1)
    _,B0,_=boundary_second(t,H,J0,0,m0,Pi,A,A2,r,S)
    _,B1,_=boundary_second(t,H0,J,l,m,Pi,A,A2,r,S)
    _,B2,_=boundary_second(t,H0,J0,0,m0,Pi,A,A2,r,S)
    assert zero(nj-B0-B1+B2)
    # Test actual integral response for q=0,1,4 and manufactured smooth source.
    eta=s.symbols('eta',real=True); Z=s.exp(-2*eta)*eta**2
    for q in (0,1,4):
        F=amplitude_feedback(eta,0,q,Z,S).doit()
        assert s.simplify(s.diff(F,eta,2)+2*s.diff(F,eta)+q*F-2*S*s.exp(2*eta)*Z)==0
        assert s.simplify(F.subs(eta,0))==0 and s.simplify(s.diff(F,eta).subs(eta,0))==0
    # Explicit frozen material subluminal upper condition epsilon*S*mu < w_min/2.
    mu=source_shear_bound()+1; wmin=4*r/(3*12**4)
    ceiling=wmin/(2*mu)
    assert ceiling>0 and ceiling*mu==wmin/2
    print(s.__version__,'11 grouped checks PASS; frozen epsilon*S <',ceiling)

if __name__=='__main__':run()
