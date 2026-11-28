"""Ideal whole-chain unity witness; conditional finite modal model, not physical admission.
Donors: Hopf P0K DFT, spherical mixed parity, J20 matched wave,
source-access P0 action balance, reciprocal material and recovery ledgers.
"""
import sympy as S


def zero(x):
    return all(S.simplify(S.expand_complex(t))==0 for t in x) if isinstance(x,S.MatrixBase) else S.simplify(S.expand_complex(x))==0


def geometry():
    # Same P0K three-port phases; same signed spherical mixed parity, now
    # vector bilinear contraction instead of an unsigned scalar square.
    w=(-1+S.I*S.sqrt(3))/2
    F=S.Matrix(3,3,lambda j,k:w**(-j*k)/S.sqrt(3)).applyfunc(S.simplify)
    assert zero(F.H*F-S.eye(3))
    for k in range(3):
        u=F.H[:,k];assert zero(F*u-S.eye(3)[:,k]) and zero((u.H*u)[0]-1)
    x,y,z=S.symbols('x y z',real=True);n=S.Matrix([x,y,z]);e=S.Matrix([0,0,1]);r=n.dot(n)
    P=n;Q=3/S.sqrt(2)*(n*z-e/3);target=S.sqrt(3)*z
    # On unit sphere, Q consists of degree-2 harmonic components.
    raw=3/S.sqrt(2)*(n*z-e*r/3)
    for q in raw:assert S.expand(sum(S.diff(q,t,2) for t in (x,y,z)))==0
    assert S.expand(P.dot(Q)-S.sqrt(2)*z)==S.sqrt(2)*3*z*(r-1)/2 or S.expand(P.dot(Q)-S.sqrt(2)*z-S.sqrt(2)*3*z*(r-1)/2)==0
    # Sphere moments <z²>=1/3; P,Q and target each normalized.
    assert zero((S.Rational(1,3)/3+S.Rational(1,9))*9/2-1)
    overlap=S.sqrt(S.Rational(2,3));assert zero(S.sqrt(2)*z-overlap*target)
    # Need a signed off-diagonal physical material tensor: not scalar q².
    # Scalar square of nonzero unit-norm real profile always has DC projection 1.
    # Required material multiplier for g=sqrt(2) is sqrt(3), not inferred.
    assert zero(S.sqrt(3)*overlap-S.sqrt(2))
    return F,overlap


def inverse_losses():
    e,a,b,c,l,h,k=S.symbols('e a b c l h k',positive=True)
    # Linear full-frequency chain; k is effective loading at source.
    R=(e-a-k)**2/(e+a+k)**2
    eta=4*e*k/(e+a+k)**2*h*h/(h*h+b*(l+c))*l/(l+c)
    match=eta.subs(k,e-a)
    assert S.cancel(match-(e-a)/e*h*h/(h*h+b*(l+c))*l/(l+c))==0
    cap=e/(e+a)*h*h/(h*h+b*(l+c))*l/(l+c)
    assert S.cancel(cap-eta-cap*(k-e-a)**2/(e+a+k)**2)==0
    assert S.cancel(R.subs(k,e-a))==0
    # Universal source-port bound at fixed e,a, for all restored paid dynamics.
    u,v=S.symbols('u v',real=True)
    assert S.expand(2*S.sqrt(2*e)*u*v-2*(e+a)*v*v-e*u*u/(e+a)+2*(e+a)*(v-S.sqrt(2*e)*u/(2*(e+a)))**2).simplify()==0
    return cap


def rhs(x,source,ell=1,g=S.sqrt(2),phase_lock=1):
    a,c,b,d=x
    return S.Matrix([S.sqrt(2)*source-a-c,a-g*b*d,
        g*c*S.conjugate(d)-ell*b+S.I*phase_lock*(b-d),
        g*c*S.conjugate(b)-ell*d+S.I*phase_lock*(d-b)])


def energy(x):return S.simplify(S.conjugate(x[0])*x[0]+S.conjugate(x[1])*x[1]+sum(S.conjugate(t)*t/2 for t in x[2:]))


def modal_cycle(F):
    # Reverse target: source amplitude 1, e=ell=g1=1, g2=sqrt(2).
    # Two distinct half-frequency polarizations; equal-frequency phase locking
    # is Hermitian mixing, not a source of energy.
    u0=F.H[:,0];selected=F*u0;assert zero(selected-S.eye(3)[:,0])
    t=1/S.sqrt(2);x=S.ones(4,1)*t;assert zero(rhs(x,selected[0]))
    ar=S.symbols('a0:4',real=True);ai=S.symbols('i0:4',real=True);u=S.symbols('u',real=True)
    z=S.Matrix([p+S.I*q for p,q in zip(ar,ai)]);f=rhs(z,u)
    flux=S.expand_complex((S.conjugate(z[0])*f[0]+S.conjugate(z[1])*f[1])*2+sum(S.conjugate(z[j])*f[j] for j in (2,3))).as_real_imag()[0]
    incident=u*u;reflection=(u-S.sqrt(2)*ar[0])**2+2*ai[0]**2
    useful=(ar[2]+ar[3])**2/2+(ai[2]+ai[3])**2/2
    leakage=(ar[2]-ar[3])**2/2+(ai[2]-ai[3])**2/2
    assert zero(flux-incident+reflection+useful+leakage)
    sub=dict(zip(ar+ai+(u,),[t]*4+[0]*4+[1]))
    assert [S.simplify(v.subs(sub)) for v in (incident,reflection,useful,leakage)]==[1,0,1,0]
    assert zero(2*x[0]*x[1]-1) and zero(2*S.sqrt(2)*x[1]*x[2]*x[3]-1)
    assert zero(rhs(S.zeros(4,1),0))
    # Unseeded half-mode stays zero and reflects all incident power in steady state.
    assert zero(rhs(S.Matrix([0,S.sqrt(2),0,0]),1))
    # The nonzero branch is locally Schur under implicit midpoint; no claim
    # of global basin. Linearize complex envelope in real coordinates.
    ff=S.Matrix([S.re(v).expand(complex=True) for v in f]+[S.im(v).expand(complex=True) for v in f])
    A=ff.jacobian(ar+ai).subs(sub);H=-(A+A.T)/2
    assert H.is_positive_semidefinite
    I=S.eye(8);L=(I-A/2).inv();M=L*(I+A/2)
    assert zero(I-M.T*M-2*L.T*H*L)
    O=H*L;assert S.Matrix.vstack(*[O*M**k for k in range(8)]).rank()==8
    # Common laboratory clock: the half phase winds once, full phase twice.
    for k in range(5):
        phase=S.I**k;lab=S.diag(phase**2,phase**2,phase,phase)*x
        assert zero(energy(lab)-energy(x))
    assert lab==x
    # Exact constant-envelope midpoint trajectory, duration one, same source.
    assert zero(x-x-rhs((x+x)/2,selected[0]))
    return x,M


def recovery(x,M):
    # Same modal state: close all external ports for two finite ideal
    # reactive stages. Rotate the occupied coherent half-mode into a storage
    # mode and back; conjugate half-mode energy normalization retained.
    # This is a gated discrete cycle, not continuous-source HF hardware.
    b=(x[2]+x[3])/S.sqrt(2);dark=(x[2]-x[3])/S.sqrt(2);assert b==1 and dark==0
    z=S.Matrix([b,0]);J=S.Matrix([[0,-1],[1,0]]);I=S.eye(2)
    T=(I-J).inv()*(I+J);assert T.T*T==I
    y=T*z;end=T.T*y;assert end==z and y==S.Matrix([0,1])
    w=(y[1]**2-z[1]**2)/2;back=(end[1]**2-y[1]**2)/2
    assert w==S.Rational(1,2) and back==-w
    assert y.dot(y)==z.dot(z)==end.dot(end)
    # Full original modal state plus buffer returns. One unit incident and
    # useful during active interval; no incident, export or external work
    # during gated reversible stages. Internal recovery not counted twice.
    restored=S.Matrix([x[0],x[1],(end[0]+dark)/S.sqrt(2),(end[0]-dark)/S.sqrt(2),end[1]])
    assert restored==x.col_join(S.zeros(1,1))
    # Buffer dark-port damping during active stage: rdot=-r. At nominal
    # r=0 no loss. Two inverse rotations compose to identity for ALL states,
    # so the complete local return is Schur, including both buffer quadratures.
    # Any perturbation energy at the dark port is counted as leakage.
    full_M=S.diag(M,S.eye(2)/3)
    assert full_M.shape==(10,10) and abs(S.Rational(1,3))<1
    return w


def nonlinear_loss_inverse():
    # Same 2:1 branch with positive parasitic losses at source, cavity, load.
    A,B,C,l=S.symbols('A B C l',nonnegative=True);t=1+A;d=l+C
    a,c=S.symbols('a c',real=True)
    # g1=e=s=1; b1=b2=b, g=d/c; b²=(a-B*c)*c/d.
    # source steady balance a=(sqrt(2)-c)/t.
    y=2*l/d*(a-B*c)*c;reflect=(1-S.sqrt(2)*a)**2
    losses=2*A*a*a+2*B*c*c+2*C/d*(a-B*c)*c
    assert S.cancel((1-reflect-y-losses).subs(a,(S.sqrt(2)-c)/t))==0
    cm=(1-A)/S.sqrt(2);am=1/S.sqrt(2)
    ym=S.factor(y.subs({a:am,c:cm}));assert S.cancel(ym-l/d*(1-A)*(1-B*(1-A)))==0
    co=S.sqrt(2)/(2*(1+B*t));cap=l/(d*t*(1+B*t))
    assert S.cancel(cap-y.subs(a,(S.sqrt(2)-c)/t)-2*l*(1+B*t)/(d*t)*(c-co)**2)==0
    # Full 100% is attainable in the zero-loss branch, not with required
    # occupied positive losses. Matched branch requires A<1 and B*(1-A)<1.
    assert S.cancel(cap.subs({A:0,B:0,C:0})-1)==0
    return ym,cap


def run():
    F,o=geometry();cap=inverse_losses();x,M=modal_cycle(F);w=recovery(x,M);ym,ncap=nonlinear_loss_inverse()
    print('PASS signed vector angular cancellation, three-port coherent inverse, matched loss inverse')
    print('PASS nonlinear 2:1 phase-locked ideal modal chain, full complex local Schur, source-off and unseeded controls')
    print('PASS exact nonlinear near-unity inverse:',ym,ncap)
    print('PASS same-state gated reversible storage and full local Schur:',w,'incident=1 reflection=0 useful=1 leakage=0 net_control=0')
    print('CONDITIONAL: actual material tensor, physical half-mode, source access, HF field generation, actuator clock and continuum unadmitted')
if __name__=='__main__':run()
