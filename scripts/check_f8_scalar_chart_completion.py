"""Complete local nonzero-k scalar chart by retaining the Tz metric row.
Exact linear source reduction and chart gauge transport; global/energy open.
"""
import sympy as s
from itertools import product

def exact():
    T,z,x=s.symbols('T z x',real=True); q=s.symbols('q',nonzero=True); X=(T,z,x); ix=range(3)
    A,B,C,D,H,J,u=[s.Function(n)(T,z) for n in 'ABCDHJu']
    eta=s.diag(-1,1,1); g=eta/z**6; gi=g.inv()
    p=s.Matrix([[H,D,B],[D,J,C],[B,C,A-H]])
    d0=lambda f,i:s.diff(f,X[i]); d=lambda f,i:q*f if i==2 else s.diff(f,X[i])
    h=p/z**6; di=-gi*h*gi
    C0={}; C1={}
    for a,b,c in product(ix,repeat=3):
        C0[a,b,c]=sum(gi[a,l]*(d0(g[l,c],b)+d0(g[l,b],c)-d0(g[b,c],l))/2 for l in ix)
        C1[a,b,c]=s.expand(sum((di[a,l]*(d0(g[l,c],b)+d0(g[l,b],c)-d0(g[b,c],l))+gi[a,l]*(d(h[l,c],b)+d(h[l,b],c)-d(h[b,c],l)))/2 for l in ix))
    Ric=s.Matrix(3,3,lambda i,j:s.expand(sum(d(C1[k,i,j],k)-d(C1[k,i,k],j) for k in ix)+sum(C0[k,k,l]*C1[l,i,j]+C1[k,k,l]*C0[l,i,j]-C0[k,j,l]*C1[l,i,k]-C1[k,j,l]*C0[l,i,k] for k,l in product(ix,repeat=2))))
    v=s.Matrix([0,-1/z,0]); du=s.Matrix([d(u,i) for i in ix]); S=(Ric-6*(v*du.T+du*v.T)+12*z**4*h-48*z**4*u*g).applyfunc(s.expand)
    U=s.diff(B,T)-q*A/2; V=s.diff(C,T)+s.diff(B,z)-q*D
    O=s.diff(V,T,2)-q*q*V-2*s.diff(U,T,z)
    assert s.expand(O-2*(s.diff(S[1,2],T)-q*S[0,1]))==0
    # Gauge solve for xi_x=c with c_TT-q² c=U; xi_T,xi_z algebraic.
    c=s.Function('c')(T,z); a=(B-s.diff(c,T))/q; b=(C-s.diff(c,z))/q
    assert s.expand(B-s.diff(c,T)-q*a)==0 and s.expand(C-s.diff(c,z)-q*b)==0
    assert s.expand(A-2*s.diff(a,T)-2*q*c-2*(s.diff(c,T,2)-q*q*c-U)/q)==0
    Dnew=D-s.diff(b,T)-s.diff(a,z)
    assert s.expand(Dnew-(2*s.diff(c,T,z)-V)/q)==0
    # All six additive source corrections of the retained offdiagonal row.
    Dpart=s.Matrix([[s.diff(D,T,z)-6*s.diff(D,T)/z,-q*q*D/2,q*(s.diff(D,z)-3*D/z)/2],[-q*q*D/2,-s.diff(D,T,z)+3*s.diff(D,T)/z,-q*s.diff(D,T)/2],[q*(s.diff(D,z)-3*D/z)/2,-q*s.diff(D,T)/2,3*s.diff(D,T)/z]])
    zero=lambda M:M.applyfunc(s.expand)==s.zeros(*M.shape)
    assert zero(S.subs({A:0,B:0,C:0,H:0,J:0,u:0}).doit()-Dpart)
    assert s.expand(2*(s.diff(Dpart[1,2],T)-q*Dpart[0,1])+q*(s.diff(D,T,2)-q*q*D))==0
    # Exact retarded oscillator kernel for q=i k, k real nonzero.
    k,tau=s.symbols('k tau',real=True,nonzero=True); K=s.sin(k*tau)/k
    assert s.diff(K,tau,2)+k*k*K==0 and K.subs(tau,0)==0 and s.diff(K,tau).subs(tau,0)==1
    # Radion equation Box_E psi-4 exp(-4 psi): D contribution from delta inverse metric.
    dens=z**-9; dp=s.Matrix([[0,D,0],[D,0,0],[0,0,0]]); dgi=-gi*(dp/z**6)*gi
    assert s.trace(gi*dp/z**6)==0
    dbox=s.diff(dens*dgi[0,1]*(-1/z),T)/dens
    assert s.expand(dbox+z**5*s.diff(D,T))==0
    # Full physical boost: Einstein-frame relative offdiag equals 5D relative offdiag.
    b0,B0=s.symbols('b0 B0',real=True); M=s.Matrix([[B0,-b0],[-b0,B0]])
    boost=M.T*s.Matrix([[0,D],[D,0]])*M
    assert zero(boost-s.Matrix([[-2*B0*b0*D,(B0**2+b0**2)*D],[(B0**2+b0**2)*D,-2*B0*b0*D]]))
    print('10 grouped exact checks PASS: source curl, chart completion, Ricci/radion and wall boost')
    return Dpart,dbox

if __name__=='__main__': exact()
