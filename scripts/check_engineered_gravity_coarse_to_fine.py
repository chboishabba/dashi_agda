"""Coarse-to-fine common receiver: conditional forward/inverse fixtures.
All candidates retain distinct physical channels. No empirical or native proof.
Natural units for symbolic metric/action fixtures; SI for Newtonian comparators.
"""
import sympy as s

def zero(v):
    return s.simplify(v)==0

def check():
    # A: static tensor/scalar shielding, independent tensor and scalar ports.
    G,T,S,t,u,y=s.symbols("G T S t u y",real=True)
    forward=t*T+u*S
    assert zero(forward.subs(t,(y-u*S)/T)-y)
    assert zero(forward.subs(u,(y-t*T)/S)-y)
    assert zero((1-forward/(T+S)).subs({t:1,u:0})-S/(T+S))
    # B: finite source-to-receiver inverse, Newtonian disk, signed density.
    r,z,g,c=s.symbols("r z g c",positive=True)
    sigma=s.symbols("sigma",real=True)
    shape=1-z/s.sqrt(z*z+r*r)
    disk=2*s.pi*G*sigma*shape
    assert zero(disk.subs(sigma,y/(2*s.pi*G*shape))-y)
    # C: massive radion exterior, derivative and tidal readouts from SAME field.
    m,b=s.symbols("m b",positive=True)
    Q=s.symbols("Q",real=True)
    phi=Q*s.exp(-m*z)/z
    accel=-b*s.diff(phi,z)
    gain=b*s.exp(-m*z)*(1+m*z)/z**2
    assert zero(accel-Q*gain)
    assert zero(accel.subs(Q,y/gain)-y)
    assert zero(s.diff(accel,z)/gain-Q*(-m-2/z+m/(1+m*z)))
    # D: signed conserved active stress: explicit compact support 3D
    # stress built from scalar potential, divergence-free identically.
    x1,x2,x3=s.symbols("x1 x2 x3",real=True)
    xyz=(x1,x2,x3)
    f=s.Function("f")(*xyz)
    lap=sum(s.diff(f,x,2) for x in xyz)
    stress=s.Matrix(3,3,lambda i,j:(lap if i==j else 0)-s.diff(f,xyz[i],xyz[j]))
    assert all(zero(sum(s.diff(stress[i,j],xyz[i]) for i in range(3))) for j in range(3))
    assert zero(s.trace(stress)-2*lap)
    # For smooth compact f, int lap f=0 by divergence theorem. Local
    # signed stress is not a freely selectable negative total mass.
    # E: two independent component currents, no charge->mass alias.
    q1,q2,m1,m2,j1,j2=s.symbols("q1 q2 m1 m2 j1 j2",real=True)
    charge=q1*j1+q2*j2; mass=m1*j1+m2*j2
    assert zero(charge.subs(j2,-q1*j1/q2))
    assert zero(mass.subs(j2,-q1*j1/q2)-j1*(m1*q2-m2*q1)/q2)
    # F: EM/GW passive two-mode exchange. Static receiver must not be
    # identified with radiative amplitude; conservation for lossless pair.
    A,B,k=s.symbols("A B k",real=True)
    Adot=-k*B; Bdot=k*A
    assert zero(2*A*Adot+2*B*Bdot)
    theta=s.symbols("theta",real=True)
    assert zero(s.cos(theta)**2+s.sin(theta)**2-1)
    # G: planar static lapse metric -N(x)^2 dt²+dx²+dy²+dz², c=1.
    # Orthogonal static observer acceleration N'/N; curvature depends N''.
    N=s.Function("N")(x1)
    metric=s.diag(-N*N,1,1,1); inv=metric.inv()
    coords=s.symbols("t x1 x2 x3",real=True)
    Gamma=[[[s.simplify(sum(inv[i,l]*(s.diff(metric[l,j],coords[k])+s.diff(metric[l,k],coords[j])-s.diff(metric[j,k],coords[l]))/2 for l in range(4))) for k in range(4)] for j in range(4)] for i in range(4)]
    Ric=s.Matrix(4,4,lambda i,j:s.simplify(sum(s.diff(Gamma[k][i][j],coords[k])-s.diff(Gamma[k][i][k],coords[j])+sum(Gamma[k][k][l]*Gamma[l][i][j]-Gamma[k][j][l]*Gamma[l][i][k] for l in range(4)) for k in range(4))))
    E=Ric-metric*s.trace(inv*Ric)/2
    assert E==s.diag(0,0,s.diff(N,x1,2)/N,s.diff(N,x1,2)/N)
    a=s.symbols("a",real=True)
    assert E.subs(N,1+a*x1).doit()==s.zeros(4)
    # Constant proper acceleration of the static congruence requires
    # N=exp(a*x), a distinct curvature/source, not Rindler.
    assert E.subs(N,s.exp(a*x1)).doit().applyfunc(s.simplify)==s.diag(0,0,a*a,a*a)
    # H: conventional lift; reaction ledger, not gravitational change.
    M,F=s.symbols("M F",positive=True)
    assert zero((F-M*g).subs(F,M*g))
    # I: finite coherent/radion response from a positive derivative action.
    K,H,ap,ax,l=s.symbols("K H ap ax l",positive=True)
    Qm=s.Matrix([[K*k*k+ap,s.I*l*k],[-s.I*l*k,H*k*k+ax+l*l/K]])
    det=(K*k*k+ap)*(H*k*k+ax)+ap*l*l/K
    assert zero(Qm.det()-det)
    assert zero(Qm.inv()[0,1]+s.I*l*k/det)
    # J: F8 receiver-first weighted transpose, generic finite exact fixture.
    # NOT the original continuum or a production trajectory.
    P=s.Matrix([[1,2],[0,1]]); W0=s.diag(2,3); W1=s.diag(5,7)
    state=s.Matrix([2,-1]); receiver=s.Matrix([1,3])
    adj=W0.inv()*P.T*W1*receiver
    assert (receiver.T*W1*P*state)==(adj.T*W0*state)
    print("PASS ten conditional coarse forward/inverse geometry and negative controls")
    print("NO physical source, actual continuum, calibrated receiver or 1g certification")

if __name__=="__main__":check()
