"""Finite source/receiver families, conditional L3-L4 all-lane refinement.
No empirical source coefficients or native/continuum certificate.
"""
import sympy as s

def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)

def shell():
    # Static thin shell between Minkowski and Schwarzschild, G=c=1.
    # Israel junction, outward normal increasing radius on both sides.
    R=s.symbols('R',positive=True)
    u=s.symbols('u',positive=True) # sqrt(1-2M/R), physical 0<u<1
    M=R*(1-u*u)/2
    sigma=(1-u)/(4*s.pi*R)
    p=((1-M/R)/u-1)/(8*s.pi*R)
    eq(p,(1-u)**2/(16*s.pi*R*u))
    eq(sigma-p,(1-u)*(5*u-1)/(16*s.pi*R*u))
    # DEC for ordinary positive-mass shell iff u>=1/5, u<1.
    # Exterior acceleration of a static observer points outward;
    # free fall relative to this congruence is inward.
    a=M/(R*R*u)
    eq(a,(1-u*u)/(2*R*u))
    eq((4*s.pi*R*R*sigma),R*(1-u))
    eq(M,4*s.pi*R*R*sigma-(4*s.pi*R*R*sigma)**2/(2*R))
    # Repulsive interior de Sitter core: positive density, p=-rho,
    # no claim about admissibility of the matching shell.
    r,H=s.symbols('r H',positive=True)
    f=1-H*H*r*r
    rho=(1-f-r*s.diff(f,r))/r**2
    pr=(f-1)/r**2+s.diff(f,r)/r
    eq(rho,3*H*H);eq(pr,-rho)
    eq(rho+3*pr,-6*H*H)
    eq(s.diff(f,r)/(2*s.sqrt(f)),-H*H*r/s.sqrt(f))
    # de Sitter interior to Schwarzschild exterior: independent shell
    # stress with proper-time matched lapse; v=sqrt(f_in), u=sqrt(f_out).
    v=s.symbols('v',positive=True)
    sig=(v-u)/(4*s.pi*R)
    pp=((1-u*u)/(2*u)+(1-v*v)/v+u-v)/(8*s.pi*R)
    eq(pp.subs(v,1),p)
    eq(pp.subs(v,u),(3*(1-u*u)/(2*u))/(8*s.pi*R))
    # At equal metric f, zero surface density but nonzero pressure:
    # not a DEC-admissible shell unless trivial.
    eq(sig.subs(v,u))

def scalar_interface():
    # Exact exterior impedance for spherical massive scalar. The boundary
    # energy follows from integrating the homogeneous field equation.
    r,R,m,q=s.symbols('r R m q',positive=True)
    phi=q*R*s.exp(-m*(r-R))/r
    eq(phi.subs(r,R),q)
    eq(-s.diff(phi,r).subs(r,R),(m+1/R)*q)
    eq(s.diff(r*r*phi*s.diff(phi,r),r),
       r*r*(s.diff(phi,r)**2+m*m*phi**2))
    # E_ext=2*pi*R²*(m+1/R)*q² in canonical natural units.
    # target gradient g/beta fixes boundary amplitude.
    b,g=s.symbols('b g',positive=True)
    qstar=g/(b*(m+1/R))
    eq((b*(-s.diff(phi,r).subs(r,R))).subs(q,qstar),g)
    eq((2*s.pi*R**2*(m+1/R)*q*q).subs(q,qstar),
       2*s.pi*R**2*g*g/(b*b*(m+1/R)))
    # Opposite consequence: relative gradient rises with mass.
    eq(s.diff(phi,r,2)/(-s.diff(phi,r)),2/r+m*m*r/(1+m*r))

def matter_and_conversion():
    # Relative-phase finite energy source: canonical sine-Gordon wall.
    x,L,J,b=s.symbols('x L J b',positive=True)
    th=4*s.atan(s.exp(x/L))
    eq(s.diff(th,x,2)*L*L,s.sin(th))
    eq(s.diff(th,x)**2*L*L/2,1-s.cos(th))
    # radion coupling to Josephson potential only, not rest mass.
    phi=s.symbols('phi',real=True)
    U=J*s.exp(b*phi)*(1-s.cos(th))
    eq(s.diff(U,phi),b*U)
    # driven loss port: stationary forward and inverse source.
    a,c,k,g1,g2,u=s.symbols('a c k g1 g2 u',positive=True)
    aa=u*g2/(g1*g2+k*k);cc=u*k/(g1*g2+k*k)
    eq(-g1*aa-k*cc+u);eq(k*aa-g2*cc)
    eq(u*aa,g1*aa*aa+g2*cc*cc)
    # external work and receiver response are distinct observables.
    eq(cc.subs(u,c*(g1*g2+k*k)/k),c)

def source_moments():
    # Smooth compact radial seed, exact weighted moment identity used
    # in original F8 source-moment donor; not native F8 propagation.
    r=s.symbols('r',positive=True)
    f=(1-r*r)**4
    D=lambda v:s.diff(v,r,2)+2*s.diff(v,r)/r
    source=D(D(f))
    for n in (0,2):
        eq(s.integrate(r**(2+n)*source,(r,0,1)))
    eq(s.integrate(r**6*source,(r,0,1)),
       120*s.integrate(r*r*f,(r,0,1)))
    # generic radial bi-Laplacian fixture is distinct from original
    # projected TT source normalization.
    # ordinary lift: force applied over height pays potential energy.
    m,g,h=s.symbols('m g h',positive=True)
    eq(s.integrate(m*g,(r,0,h)),m*g*h)

def main():
    for fn in (shell,scalar_interface,matter_and_conversion,source_moments):
        fn();print('PASS',fn.__name__,flush=True)
    print('Finite conditional geometry only; physical source and original F8 continuum OPEN')
if __name__=='__main__':main()
