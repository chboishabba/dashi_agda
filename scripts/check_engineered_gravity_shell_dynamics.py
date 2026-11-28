"""Fixed-parameter shell stability and same-action stabilization checks.
Conditional models; no apparatus or native proof.
"""
import sympy as s

def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)

def main():
    r=s.symbols('r',positive=True)
    A=1-s.Rational(7,16)*r*r
    B=1-s.Rational(2,9)/r-s.Rational(19,36)*r*r
    h=r/4
    V=(A+B)/2-h*h/4-(A-B)**2/(4*h*h)
    eq(V,-(r-1)**2*(43*r**4+86*r**3+48*r**2+32*r+16)/(81*r**4))
    eq(V.subs(r,1));eq(s.diff(V,r).subs(r,1));eq(s.diff(V,r,2).subs(r,1),-s.Rational(50,9))
    # EOS-dependent local slope eta=dP/dsigma. At P=-sigma,
    # conservation sigma'= -2(sigma+P)/r implies sigma'=sigma''=0
    # for a differentiable barotropic EOS. Changing eta alone cannot stabilize.
    eta,sig,p=s.symbols('eta sigma p',real=True)
    sp=-2*(sig+p)/r
    spp=-2*(1+eta)*sp/r+2*(sig+p)/r**2
    eq(sp.subs(p,-sig));eq(spp.subs(p,-sig))
    # General original strict DEC fixture, R normalized to one.
    A=1-s.Rational(7,16)*r*r
    B=1-s.Rational(1,4)/r-r*r/2
    H=s.Function('h')(r)
    V=(A+B)/2-H*H/4-(A-B)**2/(4*H*H)
    # sigma8 R=1/2, P8 R=-5/12; h'= -4pi(sigma+2P).
    hv={H.subs(r,1):s.Rational(1,4),s.diff(H,r).subs(r,1):s.Rational(1,6),
        s.diff(H,r,2).subs(r,1):(1+2*eta)/12}
    eq(V.subs(r,1).subs(hv));eq(s.diff(V,r).subs(r,1).subs(hv))
    curvature=s.factor(s.diff(V,r,2).subs(r,1).subs(hv))
    eq(curvature,(36*eta-325)/72)
    assert curvature.subs(eta,1)<0
    print('strict DEC shell Vpp:',curvature)
    # Conditional three-power uplift (comparison only; existing Casimir
    # spectrum is the preferred actual one-loop donor).
    b,b0,C,n=s.symbols('b b0 C n',positive=True)
    A=(n-3)*C*b0**(1-n)/2; B=-(n-1)*C*b0**(3-n)/2
    U=A/b+B/b**3+C/b**n
    eq(U.subs(b,b0));eq(s.diff(U,b).subs(b,b0))
    eq(s.diff(U,b,2).subs(b,b0),(n-1)*(n-3)*C*b0**(-n-2))
    # Original Nambu family changes parameters with R, unlike perturbation.
    print('Nambu fixed-parameter Vpp=-50/9; radial instability')
    print('PASS conditional stability and uplift identities')
if __name__=='__main__':main()
