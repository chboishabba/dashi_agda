"""F8 sourced scalar reverse bulk residual and completed-chart embedding weld.
Conditional local identities; no global chart existence or coupled coercivity.
"""
import sympy as s

def exact():
    T,z,x=s.symbols('T z x',real=True); q=s.symbols('q',nonzero=True)
    # Background Einstein frame: g=z^-6 eta, psi=-log z.
    eta=s.diag(-1,1,1); g=eta/z**6; gi=g.inv(); coords=(T,z,x)
    ix=range(3)
    C={(a,b,c):sum(gi[a,l]*(g[l,c].diff(coords[b])+g[l,b].diff(coords[c])-g[b,c].diff(coords[l]))/2 for l in ix) for a in ix for b in ix for c in ix}
    B,H=s.Function('B')(T,z),s.Function('H')(T,z)
    # After imposing Tx,zx,Tz and TT+xx rows, residual is diag(B,H,-B).
    E=s.diag(B,H,-B); A=gi*E-s.trace(gi*E)*s.eye(3)/2
    d=lambda f,i:q*f if i==2 else f.diff(coords[i])
    div=[s.expand(sum(d(A[a,j],a)+sum(C[a,a,l]*A[l,j]-C[l,a,j]*A[a,l] for l in ix) for a in ix)) for j in ix]
    assert s.expand(div[2]+q*z**6*H/2)==0
    assert s.expand(div[0]+z**6*H.diff(T)/2)==0
    assert s.expand(div[1]-z**6*(B.diff(z)+H.diff(z)/2-3*H/z))==0
    # In source-compatible residual Bianchi, div A=6 C_scalar/z in z row, zero otherwise.
    # x row forces H=0; z row then determines remaining scalar residual.
    assert s.expand(div[1].subs(H,0).doit()-z**6*(B.diff(z)))==0
    # Existing master identity gives (B/z²)_z=0, so one radial anchor kills B.
    F,Z,J=[s.Function(n)(T,z) for n in ('F','Z','J')]
    box=lambda f:-f.diff(T,2)+q*q*f
    op=lambda f:box(f)+f.diff(z,2)-f.diff(z)/z
    L=lambda f:box(f)+f.diff(z,2)-3*f.diff(z)/z
    r=Z+F/3; Jdef=F.diff(z)-6*r/z; AF=op(F)
    assert s.expand(L(Z)-z*(AF.diff(z)-op(Jdef)-Jdef/z**2)/6+AF/3-2*Jdef/(3*z))==0
    assert s.expand((B/z**2).diff(z)-(B.diff(z)-2*B/z)/z**2)==0
    # Material/embedding: retain D=h_Tz in full boost, not diagonal approximation.
    b,k=s.symbols('b k',positive=True); beta=s.sqrt(1+b*b); K,w=s.symbols('K w',positive=True)
    F,G,Z,Fn,Zn,f,ft,u,ut,v,V,jx,jy,jm,D=s.symbols('F G Z Fn Zn f ft u ut v V jx jy jm D')
    q=s.I*k*b; r=Z+F/3
    l=-2*beta**2*(F-2*r)+2*b*b*(G-2*r)-2*beta*b*D
    W=2*beta*b*(F-G)+(beta**2+b*b)*D
    lam=-2*b*b*(F-2*r)+2*beta**2*(G-2*r)-2*beta*b*D
    assert s.simplify(beta*lam/2+b*W/2-beta*(G-2*r)+b*D/2)==0
    rho=w*(q*v-F+3*beta*f)+K*(ut+l/2+f/beta)-3*b*K*u
    rhog=b*b*f-beta*lam/2-b*W-Zn-Fn/3-b*ft+jy
    diff=3*Zn-k*k*b*b*f+jx-jy
    mix=q*(W/2+ft-b*f)-3*(w*V+K*q*u)-jm
    c=k*k*b*b/3+3*w*beta+K/beta
    rhs=-w*(q*v-F)-K*(ut+l/2)-beta*(G-2*r)+b*D/2-Fn/3-b*(3*w*V+jm)/q+(jx+2*jy)/3
    assert s.simplify(q*(rho-rhog)-q*(c*f-rhs)-q*diff/3-b*mix)==0
    assert s.simplify((rho-rhog).subs({Zn:s.solve(diff,Zn)[0],ft:s.solve(mix,ft)[0]})-(c*f-rhs))==0
    print('9 exact checks PASS: reverse bulk Bianchi, anchor and completed-chart embedding')

if __name__=='__main__':exact()
