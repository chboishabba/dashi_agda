"""Alternative mechanism cut: nonminimal tensor, dynamical virial, topology.
Standard scalar-tensor and virial identities; conditional EFT, not a device.
Donors: OCT369 P023 stress Ward, KK Derrick, F8 quadratic Einstein.
"""
import sympy as s

def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)

def tensor():
    # Tensor quadratic action with positive effective Planck mass F(x).
    # Mode equation (F h')'+omega² F h=0, no surface tensor source.
    # Matching h and F h' at an abrupt interface; propagating mode only.
    f,g,w=s.symbols('F1 F2 omega',positive=True)
    R,T=s.symbols('R T',real=True)
    sol=s.solve([1+R-T,f*(1-R)-g*T],(R,T))
    eq(sol[R],(f-g)/(f+g));eq(sol[T],2*f/(f+g))
    eq(sol[R]**2+g/f*sol[T]**2,1)
    # Finite layer between identical exterior regions, phase theta.
    th=s.symbols('theta',real=True)
    P=s.Matrix([[s.cos(th),s.sin(th)/(g*w)],[-g*w*s.sin(th),s.cos(th)]])
    eq(P.det(),1)
    assert P.subs(th,0)==s.eye(2)
    # Static homogeneous 1D flux: no sink; gradient adjusts inversely.
    j,d=s.symbols('j d',real=True)
    eq(g*(j/g),f*(j/f))
    # Not a Newtonian shielding calculation: scalar constraints and
    # background F, metric and material equations must be solved together.
    # Scalar-tensor E-frame canonical metric coefficient for F>0.
    phi,M,K=s.symbols('phi M K',positive=True)
    xi=s.symbols('xi',nonnegative=True)
    F=M*M+2*xi*phi*phi
    kinetic=M*M*(K/F+s.Rational(3,2)*(s.diff(F,phi)/F)**2)
    assert kinetic.is_positive
    # Universal Jordan matter coupling A=M/sqrt(F), derivative is fixed.
    eq(s.diff(s.log(M/s.sqrt(F)),phi),-s.diff(F,phi)/(2*F))

def dynamical():
    # Compact isolated conserved stress: I''=2 int T_ii in c=1.
    # Periodic bounded I has zero mean second derivative; instantaneous
    # stress need not vanish. Illustrative quadrupole moment.
    t,w,I0,a=s.symbols('t w I0 a',positive=True)
    I=I0+a*s.cos(w*t)
    trace=s.diff(I,t,2)/2
    eq(s.integrate(trace,(t,0,2*s.pi/w)))
    # Retarded observable cannot be inferred from instantaneous active sum.
    # Source-free monochromatic tidal oscillation and nonlinear rectifier
    # are distinct observables, with nonnegative square mean.
    y=a*s.cos(w*t)
    eq(s.integrate(y,(t,0,2*s.pi/w)))
    eq(w/(2*s.pi)*s.integrate(y*y,(t,0,2*s.pi/w)),a*a/2)

def topology():
    # Standard Skyrme-like scaling, not an actual Hopf solution.
    R,A,B,C=s.symbols('R A B C',positive=True)
    E=A*R+B/R+C*R**3
    eq(s.diff(E,R).subs(B,A*R**2+3*C*R**4))
    eq(s.diff(E,R,2).subs(B,A*R**2+3*C*R**4),2*A/R+12*C*R)
    # Full trace under dilation is -R dE/dR for isolated static source.
    # At equilibrium it vanishes regardless of topological sector.
    eq((-R*s.diff(E,R)).subs(B,A*R**2+3*C*R**4))
    # 4-spatial-dimensional YM scale invariant; R^3 energy scaling
    # cannot be transferred to 4 spatial dimensions without rederivation.
    n,p=s.symbols('n p',integer=True,positive=True)
    eq((n-2*p).subs({n:4,p:2}))

def receiver():
    # Relative mode with independent source and sensor; finite matrix
    # transfer. This is a reciprocity diagnostic, not native F8.
    a,b,c,d=s.symbols('a b c d',real=True)
    H=s.Matrix([[a,c],[c,b]])
    S=s.Matrix([1,0]);D=s.Matrix([0,d])
    eq((D.T*H.inv()*S)[0],(S.T*H.inv()*D)[0])
    # Independent nuisance channel: source identity alone is insufficient.
    X,Y=s.symbols('X Y',real=True)
    eq((X+Y).subs(Y,-X))
    print('PASS conditional reciprocity and independent nuisance cancellation')

if __name__=='__main__':
    for fn in (tensor,dynamical,topology,receiver):
        fn();print('PASS',fn.__name__,flush=True)
    print('OPEN physical F(O), scalar constraints, topological source, nonlinear receiver and original F8')
