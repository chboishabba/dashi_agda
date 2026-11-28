"""Static scalar-tensor constraints and finite-layer receiver limits.
Standard linearized scalar-tensor theory around constant flat vacuum.
Conditional models, no actual material F or native F8 evolution.
"""
import sympy as s

def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)

def static():
    # Metric -(1+2Phi)dt²+(1-2Psi)dx²; F=F0+f*varphi.
    # Fourier Laplacian -k²; source nonrelativistic rho, U'=U=0.
    F,K,m,k=s.symbols('F K m k',positive=True)
    f,rho=s.symbols('f rho',real=True)
    P,S,q=s.symbols('Phi Psi varphi')
    D=K+3*f*f/(2*F)
    rows=[-2*F*k*k*S-rho+k*k*f*q,
          F*(S-P)-f*q,
          -(K*k*k+m*m)*q+f*k*k*(P-2*S)]
    sol=s.solve(rows,(P,S,q))
    eq(sol[q],f*rho/(2*F*(D*k*k+m*m)))
    eq(sol[P],-rho/(2*F*k*k)-f*sol[q]/(2*F))
    eq(sol[S],-rho/(2*F*k*k)+f*sol[q]/(2*F))
    # Same light deflection combination independent of scalar at fixed F.
    eq(sol[P]+sol[S],-rho/(F*k*k))
    eq(sol[P].subs(f,0),-rho/(2*F*k*k))
    # Positive scalar residue, no cancellation for identical universal
    # coupling and positive kinetic/mass in this homogeneous model.
    eq(sol[P]/(-rho/(2*F*k*k))-1,f*f*k*k/(2*F*(D*k*k+m*m)))

def layer():
    # Two identical exterior half spaces; finite interior tensor slab.
    # Dimensionless phase theta=omega*d, contrast z=F2/F1.
    z,t=s.symbols('z theta',positive=True,real=True)
    P=s.Matrix([[s.cos(t),s.sin(t)/z],[-z*s.sin(t),s.cos(t)]])
    I=s.I
    basis=s.Matrix([[1,1],[I,-I]])
    W=s.simplify(basis.inv()*P*basis)
    eq(W.det(),1)
    amp=1/W[1,1]
    flux=s.simplify(amp*s.conjugate(amp))
    target=1/(1+(z-1/z)**2*s.sin(t)**2/4)
    eq(flux,target)
    eq(flux.subs(t,0),1)
    eq(flux.subs(t,s.pi),1)
    eq(flux.subs(z,1),1)
    # Static limit at fixed finite contrast and thickness is transparent
    # in propagating-wave scattering, not a static Poisson solution.
    eq(s.limit((1-target)/t**2,t,0),(z-1/z)**2/4)

def nonlinear():
    # Two coherent modes: signed DC cross term retains relative phase.
    t,w,a,b,p=s.symbols('t w a b p',real=True)
    # use phase as independent cosine/sine coefficients for exact mean
    c,d=s.symbols('c d',real=True)
    x=a*s.cos(t); y=c*s.cos(t)+d*s.sin(t)
    avg=lambda v:s.integrate(s.expand_trig(v),(t,0,2*s.pi))/(2*s.pi)
    eq(avg(x*y),a*c/2)
    eq(avg((x+y)**2),((a+c)**2+d*d)/2)
    # This is source algebra only. Retarded inverse and metric receiver
    # are not interchangeable with detector rectification.
    # Weighted source budget: exact Cauchy remainder for two modes.
    eq((a*a+b*b)*(c*c+d*d)-(a*c+b*d)**2,(a*d-b*c)**2)

def topology():
    # Positive nonminimal action in Einstein frame, scalar field metric.
    F,K,M,f=s.symbols('F K M f',positive=True)
    G=M*M*(K/F+3*f*f/(2*F*F))
    assert G.is_positive
    # Finite conformal change localized away from source and receiver
    # cannot be treated as freely chosen matter-frame force there.
    beta=-f/(2*F)
    eq(beta**2/G,f*f/(M*M*(4*K*F+6*f*f)))

if __name__=='__main__':
    for fn in (static,layer,nonlinear,topology):
        fn();print('PASS',fn.__name__,flush=True)
    print('OPEN inhomogeneous background and material action, original F8 nonlinear retarded solution, physical receiver')
