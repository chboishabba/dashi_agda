"""Joint causal LC and conserved HF-action family, exact local return.
The complex quadrature model is conditional, not atmospheric Maxwell admission.
"""
import sympy as S
from solar_steelman_network_converter import run as network, branch
from solar_steelman_unity import zero


def run():
    X,f,coords,sub,A,G,physical=network(); a,c,b,d=X[:4]
    I=S.I; chi=S.sqrt(2); J=S.symbols('J',positive=True)
    g=chi*J; L,_=branch(S.Integer(1),S.Integer(2))
    # Same LC equations, actual reciprocal coupling controlled by conserved action.
    f[1]-=(g-chi)*b*d
    f[2]+=(g-chi)*c*S.conjugate(d)/(1+L)
    f[3]+=(g-chi)*c*S.conjugate(b)/(1+L)
    K=S.conjugate(c)*b*d-c*S.conjugate(b)*S.conjugate(d)
    assert zero(K+S.conjugate(K))
    pr,pi,qr,qi=S.symbols('pr pi qr qi',real=True);p=pr+I*pi;q=qr+I*qi
    action=p*S.conjugate(p)+q*S.conjugate(q)
    fh=S.Matrix([-chi*K*p,-chi*K*q]) # co-rotating HF frame
    assert zero(2*S.re(S.conjugate(p)*fh[0]+S.conjugate(q)*fh[1]))
    # Physical normalized energy: unchanged balance for all actions and phases.
    sr,si=S.symbols('sr si',real=True);s=sr+I*si
    balance=S.re(sum(w*S.conjugate(z)*v for w,z,v in zip(physical,X,f)))
    reflect=s-S.sqrt(2)*a
    assert zero(balance-s*S.conjugate(s)+reflect*S.conjugate(reflect)+b*S.conjugate(b)+d*S.conjugate(d))
    # Exact real equilibrium family, for action J>1/2. LC states retain
    # the same signed phase relation, not just their magnitudes.
    aa=S.sqrt(2)-1/g;cc=1/g;bb=S.sqrt(aa/g)
    eq=[aa,cc,bb,bb]+[0]*9
    for index,offset,w,v in [(0,4,S.Integer(2),S.Integer(1)),(2,7,S.Integer(1),S.Integer(2)),(3,10,S.Integer(1),S.Integer(2))]:
        t=eq[index];eq[offset:offset+3]=[t/(I*w),I*w*t/(v*v-w*w),t/(v*v-w*w)]
    # Use positive real amplitudes explicitly, avoiding symbolic branch ambiguity.
    bb0=S.symbols('B',positive=True);ee=[z.subs(bb,bb0) for z in eq]
    # Direct complex substitution uses independent real/imag coordinates.
    eqsub=dict(zip(coords,[S.re(z) for z in ee]+[S.im(z) for z in ee]));eqsub.update({sr:1,si:0})
    assert zero(f.subs(eqsub,simultaneous=True).subs(bb0**2,aa/g))
    assert zero(K.subs(eqsub,simultaneous=True))
    reflected=S.simplify((1-S.sqrt(2)*aa)**2);useful=S.simplify(2*aa/g)
    assert S.cancel(reflected+useful-1)==0
    assert S.cancel(reflected-(1-1/J)**2)==0
    # Tangent to equilibrium family at J=1 (real positive square root).
    eq1=[z.subs(J,1) for z in eq];assert zero(S.Matrix(eq1)-X.subs(sub))
    dx=[S.diff(z,J).subs(J,1) for z in eq];v=S.Matrix([S.re(z) for z in dx]+[S.im(z) for z in dx])
    Freal=S.Matrix([S.re(z).expand(complex=True) for z in f]+[S.im(z).expand(complex=True) for z in f])
    B=Freal.diff(J).subs(sub).subs(J,1);assert zero(A*v+B)
    # Full co-rotating Jacobian at p=1,q=0. J perturbation =2 delta pr.
    hfcoords=(pr,pi,qr,qi);hsub={pr:1,pi:0,qr:0,qi:0}
    Fh=S.Matrix([S.re(fh[0]),S.im(fh[0]),S.re(fh[1]),S.im(fh[1])]).expand(complex=True)
    C=Fh.jacobian(coords).subs(sub).subs(hsub)
    D=Fh.jacobian(hfcoords).subs(sub).subs(hsub);assert D==S.zeros(4)
    V=v*S.Matrix([[2,0,0,0]]);assert zero(C*V)
    JJ=A.row_join(B*S.Matrix([[2,0,0,0]])).col_join(C.row_join(D))
    T=S.eye(30);T[:26,26:]=V
    expected=A.row_join(S.zeros(26,4)).col_join(C.row_join(S.zeros(4)))
    assert zero(JJ*T-T*expected)
    # Stable quotient plus semisimple four-dimensional neutral fibre.
    assert A.det()!=0
    W=S.eye(30);W[26:,:26]=C*A.inv()
    assert zero(expected*W-W*S.diag(A,S.zeros(4)))
    # Common normalized carrier clock, half angular frequency 1. HF
    # carrier ratio 7800/3.915=520000/261. Rotate two HF envelope stores
    # once in the common period; all physical quadrature states restore.
    t=S.symbols('t',real=True);T=2*S.pi*261;rot=1/S.Integer(261)
    hp=S.cos(rot*t);hq=S.sin(rot*t)
    assert zero(S.diff(hp,t)+rot*hq) and zero(S.diff(hq,t)-rot*hp)
    assert S.trigsimp(hp**2+hq**2)==1
    assert hp.subs(t,T)==1 and hq.subs(t,T)==0
    assert all(S.exp(I*w*T)==1 for w in (1,2,S.Rational(520000,261)))
    assert zero(K.subs(eqsub,simultaneous=True))
    assert S.simplify(S.integrate(useful.subs(J,1),(t,0,T))/T)==1
    # Startup discriminator: at unseeded c=sqrt(2), parametric gain 2.
    # For symmetric b=d perturbations, eliminate actual low-band LC states.
    w=S.Integer(1);v0=S.Integer(2);L0,K0=branch(w,v0);lam=S.symbols('lam',nonnegative=True)
    z=lam+I*w;Z=L0*z+K0/z+z/(z*z+v0*v0)
    det=S.cancel((lam+1+Z)*(lam+1+S.conjugate(Z))-4)
    assert S.simplify(det.subs(lam,0))==-3 and S.simplify(det.subs(lam,1))>0
    # Denominators are nonzero for real lambda>=0 since w=1 != v0.
    # IVT gives positive real eigenvalue; not global seeded basin.
    print('PASS joint HF/LC arbitrary-state ledger, exact action-indexed equilibria and reflection (1-1/J)^2')
    print('PASS 30-dimensional co-rotating linearization: 26 stable, 4 semisimple neutral; exact return on nominal orbit')
    print('PASS unseeded positive real eigenvalue bracket (0,1); no global startup claim')
if __name__=='__main__':run()
