"""All-lane L3 refinement: finite source geometry and independent receiver.
Conditional analytic fixtures, not a physical device or full coupled solution.
"""
import sympy as s

def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)

def interface():
    # Scalar finite spherical shell: q=r phi; regular interior and decaying
    # exterior. Match phi and phi' (same kinetic coefficient), hence q,q'.
    r,R,m,Q=s.symbols('r R m Q',positive=True)
    u=Q*s.sinh(m*r)/r
    v=Q*s.sinh(m*R)*s.exp(-m*(r-R))/r
    eq((u-v).subs(r,R))
    jump=s.simplify(s.diff(v-u,r).subs(r,R))
    eq(jump,-Q*m*s.exp(m*R)/R)
    # The derivative jump is the explicit shell source, not free shielding.
    # Independent tensor channel remains unchanged.
    eq(s.diff(v,r),-v*(m+1/r))

def focusing_and_stress():
    # Finite multipolar source, harmonic exterior in the Newtonian limit.
    r,z=s.symbols('r z',positive=True)
    c=s.symbols('c',real=True)
    for l in range(5):
        P=s.legendre(l,z)
        f=c*r**(-l-1)
        eq(s.diff(r*r*s.diff(f,r),r)*P+f*s.diff((1-z*z)*s.diff(P,z),z))
    # Compact pressure generator is invisible outside its support even
    # when non-spherical; this is a scoped weak-field source kernel.
    x,y,w=s.symbols('x y w',real=True)
    f=s.Function('f')(x,y,w)
    xyz=(x,y,w)
    L=lambda u:sum(s.diff(u,a,2) for a in xyz)
    T=s.Matrix(3,3,lambda i,j:(L(f) if i==j else 0)-s.diff(f,xyz[i],xyz[j]))
    eq(s.trace(T),2*L(f))
    assert all(s.simplify(sum(s.diff(T[i,j],xyz[i]) for i in range(3)))==0 for j in range(3))

def radion_material():
    # A specified two-component phase model, not measured GL parameters.
    x=s.symbols('x',real=True)
    K1,K2,q=s.symbols('K1 K2 q',positive=True)
    t1,t2,A=[s.Function(n)(x) for n in ('t1','t2','A')]
    D1=s.diff(t1,x)-q*A;D2=s.diff(t2,x)-q*A
    common=(K1*D1+K2*D2)/(K1+K2)
    rel=D1-D2
    eq(K1*D1**2+K2*D2**2,(K1+K2)*common**2+K1*K2/(K1+K2)*rel**2)
    # Relative mode alone is electrically dark for this model, not
    # automatically mass-current dark or a large radion source.
    j=q*(K1*D1+K2*D2)
    eq(j.subs(s.diff(t2,x),q*A-K1*D1/K2))
    phi,b,J,theta=s.symbols('phi b J theta',real=True)
    U=J*s.exp(b*phi)*(1-s.cos(theta))
    eq(s.diff(U,phi,theta),b*J*s.exp(b*phi)*s.sin(theta))
    eq(s.diff(U,phi,theta).subs(theta,0))

def conversion():
    # Damped reciprocal ports: exact work and loss ledger, independent
    # drive. Real quadrature fixture; no gravitational vertex assumed.
    a,b,k,g1,g2,u=s.symbols('a b k g1 g2 u',real=True)
    da=-g1*a-k*b+u;db=k*a-g2*b
    eq(a*da+b*db,a*u-g1*a*a-g2*b*b)
    # Static drive does not certify a gravitational wave.
    eq(db.subs(b,k*a/g2))

def metric_and_receiver():
    # Finite spherical lapse and mass function, independently compute
    # Einstein tensor from metric, then compare inverse source equations.
    t,r,th,ph=s.symbols('t r theta phi',real=True)
    f=s.Function('f')(r);N=s.Function('N')(r)
    coords=(t,r,th,ph)
    g=s.diag(-N*N,1/f,r*r,r*r*s.sin(th)**2);gi=g.inv()
    D=lambda a,i:s.diff(a,coords[i])
    C=[[[s.simplify(sum(gi[a,l]*(D(g[l,j],i)+D(g[l,i],j)-D(g[i,j],l))/2 for l in range(4))) for j in range(4)] for i in range(4)] for a in range(4)]
    Ric=s.Matrix(4,4,lambda i,j:s.simplify(sum(D(C[k][i][j],k)-D(C[k][i][k],j)+sum(C[k][k][l]*C[l][i][j]-C[k][j][l]*C[l][i][k] for l in range(4)) for k in range(4))))
    E=(gi*Ric-s.eye(4)*s.trace(gi*Ric)/2).applyfunc(s.simplify)
    rho=(1-f-r*s.diff(f,r))/r**2
    pr=(f-1)/r**2+2*f*s.diff(N,r)/(r*N)
    pt=pr+r*(s.diff(pr,r)+(rho+pr)*s.diff(N,r)/N)/2
    assert (E-s.diag(-rho,pr,pt,pt)).applyfunc(s.simplify)==s.zeros(4)
    # Compact lapse deformation, flat exterior. Inverse stress only;
    # zero density with nonzero pressure fails dominant energy condition.
    R,a=s.symbols('R a',positive=True)
    lapse=1+a*(R*R-r*r)**4
    eq(lapse.subs(r,R),1);eq(s.diff(lapse,r).subs(r,R))
    eq(rho.subs(f,1).doit())
    assert s.simplify(pr.subs({f:1,N:lapse}).doit())!=0

def lift_and_f8():
    # Conventional source/reaction and receiver residual ledger.
    F,m,g=s.symbols('F m g',real=True)
    eq((F-m*g).subs(F,m*g))
    # Linearized curvature in 1+1 receiver slice, independent of time
    # slicing gauge and spatial displacement gauge. h00=-2P,h01=B,h11=H.
    t,x=s.symbols('t x',real=True)
    P,B,H,xi,eta=[s.Function(n)(t,x) for n in ('P','B','H','xi','eta')]
    R=s.diff(P,x,2)+s.diff(B,t,x)-s.diff(H,t,2)/2
    sub={P:P+s.diff(xi,t),B:B-s.diff(xi,x)+s.diff(eta,t),H:H+2*s.diff(eta,x)}
    eq(R.subs(sub,simultaneous=True).doit(),R)
    # This tidal observable is not a uniform acceleration measurement.
    eq(R.subs({P:g*x,B:0,H:0}).doit())

def main():
    for fn in (interface,focusing_and_stress,radion_material,conversion,metric_and_receiver,lift_and_f8):
        fn();print('PASS',fn.__name__,flush=True)
    print('Conditional source/metric/receiver refinements only; actual material and bulk sources OPEN')

if __name__=='__main__':main()
