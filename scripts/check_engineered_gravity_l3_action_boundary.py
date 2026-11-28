"""All-candidate L3: conditional action, boundary and receiver welds.

Coarse-to-fine successor of check_engineered_gravity_coarse_to_fine.
Natural units except where specified. These are exact model constructions,
not derived material coefficients, a complete 5D solution, or observations.
"""
import sympy as s

def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)

def shielding_hybrid():
    # E=1/2 q'^T K q' + q'^T C q + 1/2 q^T V q - j^T q.
    # Unlike the previous C=0 interface, this includes the derivative vertex.
    k,h,a,b=s.symbols('k h a b',positive=True)
    l=s.symbols('l',real=True)
    K=s.diag(k,h); C=s.Matrix([[0,-l],[0,0]])
    V=s.diag(a,b+l*l/k)
    assert s.simplify(V-C.T*K.inv()*C)==s.diag(a,b)
    n=2; I=s.eye(n); Z=s.zeros(n)
    J=Z.row_join(I).col_join((-I).row_join(Z))
    L=(-K.inv()*C).row_join(K.inv()).col_join(
        (V-C.T*K.inv()*C).row_join(C.T*K.inv()))
    assert (L.T*J+J*L).applyfunc(s.simplify)==s.zeros(4)
    x=s.symbols('x',real=True)
    q=s.Matrix([s.Function('phi')(x),s.Function('X')(x)])
    p=K*q.diff(x)+C*q
    j=V*q+C.T*q.diff(x)-p.diff(x)
    y=q.col_join(p)
    assert (y.diff(x)-L*y-s.zeros(2,1).col_join(-j)).applyfunc(s.simplify)==s.zeros(4,1)
    # At an interface without surface source, q,p are continuous.
    # q' is generally NOT continuous when C or K changes.
    q0=s.Matrix([1,2]);p0=s.Matrix([3,4])
    left=K.inv()*(p0-C*q0)
    right=K.inv()*p0
    assert (left-right).subs(l,1)!=s.zeros(2,1)
    # Same external scalar gradient, not merely transmitted amplitude.
    # If tensor sector unmodified and both baseline attractions positive:
    T,S,tau=s.symbols('T S tau',positive=True)
    eq(1-(T+tau*S)/(T+S),S*(1-tau)/(T+S))

def focusing():
    # Coarse weak-field potential of a compact spherical source, signed
    # source normalization retained; adjoint receiver is a Green functional.
    r,R,rho,G=s.symbols('r R rho G',positive=True)
    M=4*s.pi*rho*R**3/3
    inside=-2*s.pi*G*rho*(R*R-r*r/3)
    outside=-G*M/r
    lap=lambda f:s.diff(r*r*s.diff(f,r),r)/r**2
    eq(lap(inside),4*s.pi*G*rho);eq(lap(outside))
    eq(inside.subs(r,R),outside.subs(r,R))
    eq(s.diff(inside,r).subs(r,R),s.diff(outside,r).subs(r,R))
    # Realized monopole geometry, not a bulk focusing amplification proof.
    eq(-s.diff(outside,r),-G*M/r**2)

def radion():
    # Canonical E-frame conformal coupling and uniform finite sphere:
    # same scalar solution produces both acceleration and clock shift.
    r,R,m,S,M=s.symbols('r R m S M',positive=True)
    A=-S*(m*R+1)*s.exp(-m*R)/m**3
    B=S*(m*R*s.cosh(m*R)-s.sinh(m*R))/m**3
    u=S/m**2+A*s.sinh(m*r)/r; v=B*s.exp(-m*r)/r
    op=lambda f:s.diff(r*r*s.diff(f,r),r)/r**2-m*m*f
    eq(op(u),-S);eq(op(v))
    eq((u-v).subs(r,R));eq(s.diff(u-v,r).subs(r,R))
    beta=-1/(s.sqrt(6)*M)
    clock=beta*v; accel=-s.diff(clock,r)
    target=s.symbols('target',real=True)
    kernel=s.diff(accel,S)
    eq(accel.subs(S,target/kernel),target)
    # Scalar stress conservation requires matter exchange where S != 0.
    x=s.symbols('x',real=True);phi=s.Function('phi')(x)
    pressure=(s.diff(phi,x)**2-m*m*phi**2)/2
    eq(s.diff(pressure,x),s.diff(phi,x)*(s.diff(phi,x,2)-m*m*phi))

def active_stress():
    # Closed static stress generator, radial compact support with C1 matching.
    # The pressure contribution 2 Lap f has zero integrated monopole.
    r,R,G=s.symbols('r R G',positive=True)
    f=(R*R-r*r)**4
    lap=s.diff(f,r,2)+2*s.diff(f,r)/r
    pr=2*s.diff(f,r)/r;pt=s.diff(f,r,2)+s.diff(f,r)/r
    eq(s.diff(pr,r)+2*(pr-pt)/r)
    eq(pr+2*pt,2*lap)
    eq(pr.subs(r,R));eq(pt.subs(r,R))
    eq(s.integrate(2*lap*r*r,(r,0,R)))
    # Pressure-generated weak-field potential 8 pi G f matches zero outside.
    U=8*s.pi*G*f
    eq(s.diff(U,r,2)+2*s.diff(U,r)/r,4*s.pi*G*(pr+2*pt))
    eq(U.subs(r,R));eq(s.diff(U,r).subs(r,R))
    # This family changes interior response but cannot generate an exterior
    # acceleration from pressure alone. No physical support EOS inferred.

def material():
    # Gauge-covariant phase stiffness action in an explicit 1D local model.
    x=s.symbols('x',real=True);q,K=s.symbols('q K',positive=True)
    th,A,chi=[s.Function(n)(x) for n in ('theta','A','chi')]
    D=s.diff(th,x)-q*A
    E=K*D**2/2
    eq(D.subs({th:th+q*chi,A:A+s.diff(chi,x)},simultaneous=True).doit(),D)
    current=-s.diff(E,A)
    eq(current,q*K*D)
    eq(s.diff(E,s.diff(th,x)),K*D)
    eq(s.diff(current,x),q*s.diff(K*D,x))
    # Actual mass current still needs component mass/density/velocity.
    j1,j2,m1,m2,q1,q2=s.symbols('j1 j2 m1 m2 q1 q2',real=True)
    eq((m1*j1+m2*j2).subs(j2,-q1*j1/q2),j1*(m1*q2-m2*q1)/q2)
    # Coherent Leggett energy is a source only through actual coupling.
    phi,r,J,beta=s.symbols('phi r J beta',real=True)
    U=J*s.exp(beta*phi)*(1-s.cos(r))
    eq(s.diff(U,phi,r).subs(r,0))
    eq(s.diff(U,phi),beta*U)

def conversion():
    # Lossless signed coupled wave ports with detuning. Reciprocity and
    # norm balance are necessary, not a physical gravitational vertex.
    g,d,t=s.symbols('g d t',real=True)
    H=s.Matrix([[d,g],[g,-d]])
    w=s.sqrt(d*d+g*g)
    eq((H*H)[0,0],w*w);eq((H*H)[0,1])
    U=s.cos(w*t)*s.eye(2)-s.I*s.sin(w*t)*H/w
    assert (U.diff(t)+s.I*H*U).applyfunc(s.simplify)==s.zeros(2)
    assert (U.conjugate().T*U-s.eye(2)).applyfunc(s.simplify)==s.zeros(2)
    prob=s.simplify(U[1,0]*s.conjugate(U[1,0]))
    eq(prob,g*g*s.sin(w*t)**2/w**2)

def warp():
    # Exact static spherical inverse geometry, area radius gauge.
    # G^t_t=-2m'/r²; G^r_r=-2m/r³+2(1-2m/r)Phi'/r.
    r=s.symbols('r',positive=True);m=s.Function('m')(r);P=s.Function('Phi')(r)
    f=1-2*m/r
    rho=2*s.diff(m,r)/r**2
    pr=-2*m/r**3+2*f*s.diff(P,r)/r
    # Bianchi fixes tangential pressure, independent residual kept.
    pt=pr+r*(s.diff(pr,r)+(rho+pr)*s.diff(P,r))/2
    eq(s.diff(pr,r)+(rho+pr)*s.diff(P,r)+2*(pr-pt)/r)
    # Receiver static proper acceleration sqrt(f) Phi'; free fall distinct.
    a=s.symbols('a',real=True)
    eq((s.sqrt(f)*s.diff(P,r)).subs(s.diff(P,r),a/s.sqrt(f)),a)
    # Recover Schwarzschild vacuum exactly, rather than infer a drive.
    M=s.symbols('M',positive=True)
    sub={m:M,P:s.log(1-2*M/r)/2}
    for v in (rho,pr,pt):eq(v.subs(sub).doit())

def lift():
    # Source/receiver relative coordinate energy; reaction not optional.
    z,y=s.symbols('z y',real=True);U=s.Function('U')(z-y)
    Fz=-s.diff(U,z);Fy=-s.diff(U,y)
    eq(Fz+Fy)
    vz,vy=s.symbols('vz vy',real=True)
    eq(s.diff(U,z)*vz+s.diff(U,y)*vy+Fz*vz+Fy*vy)

def f8():
    # Actual wall master flux donor, separate source/coupled geometry.
    from check_f8_scalar_master_flux_weld import exact as flux
    from check_f8_scalar_density_momentum_schur import exact as schur
    from check_f8_scalar_chart_trace import exact as chart
    flux();schur();chart()
    # Linear induced 4D scalar metric receiver in fixed local chart:
    # ds²=-(1+2Phi)dt²+2 B_i dt dx^i+(delta_ij+h_ij)dx^i dx^j.
    # slow coordinate acceleration -grad Phi - partial_t B_i;
    # reference/gauge and physical brane reconstruction still required.
    t,x=s.symbols('t x',real=True)
    P=s.Function('Phi')(t,x);B=s.Function('B')(t,x)
    gamma=s.diff(B,t)+s.diff(P,x)
    xi=s.Function('xi')(t,x)
    eq(gamma.subs({P:P+s.diff(xi,t),B:B-s.diff(xi,x)},simultaneous=True).doit(),gamma)

def main():
    for fn in (shielding_hybrid,focusing,radion,active_stress,material,conversion,warp,lift,f8):
        fn();print('PASS',fn.__name__,flush=True)
    print('Conditional L3 model equations only; physical coefficients, global geometry and continuum acceptance OPEN')

if __name__=='__main__':main()
