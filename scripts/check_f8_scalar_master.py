"""Nonzero-k scalar Einstein-frame master, sourced bulk reconstruction; wall not closed."""
import sympy as s
from itertools import product

def exact():
    T,z,x=s.symbols('T z x',real=True); X=(T,z,x); ix=range(3); E=s.diag(-1,1,1)
    F,G,u=[s.Function(a)(*X) for a in ('F','G','u')]; g=E/z**6; gi=g.inv(); h=s.diag(-2*F,2*G,2*F)/z**6; di=-gi*h*gi
    C0={}; C1={}
    for a,b,c in product(ix,repeat=3):
        C0[a,b,c]=sum(gi[a,l]*(g[l,c].diff(X[b])+g[l,b].diff(X[c])-g[b,c].diff(X[l]))/2 for l in ix)
        C1[a,b,c]=s.expand(sum((di[a,l]*(g[l,c].diff(X[b])+g[l,b].diff(X[c])-g[b,c].diff(X[l]))+gi[a,l]*(h[l,c].diff(X[b])+h[l,b].diff(X[c])-h[b,c].diff(X[l])))/2 for l in ix))
    R=s.Matrix(3,3,lambda i,j:s.expand(sum(C1[k,i,j].diff(X[k])-C1[k,i,k].diff(X[j]) for k in ix)+sum(C0[k,k,l]*C1[l,i,j]+C1[k,k,l]*C0[l,i,j]-C0[k,j,l]*C1[l,i,k]-C1[k,j,l]*C0[l,i,k] for k,l in product(ix,repeat=2))))
    p=s.Matrix([0,-1/z,0]); du=s.Matrix([u.diff(a) for a in X]); D=(R-6*(p*du.T+du*p.T)+12*z**4*h-48*z**4*u*g).applyfunc(s.expand)
    box=lambda f:-f.diff(T,2)+f.diff(x,2)
    L=lambda f:box(f)+f.diff(z,2)-3*f.diff(z)/z
    A=lambda f:box(f)+f.diff(z,2)-f.diff(z)/z
    J=F.diff(z)-6*u/z
    B=A(F)
    assert s.expand(D[0,2]+G.diff(T,x))==0
    assert s.expand(D[0,0]+D[2,2]+G.diff(T,2)+G.diff(x,2))==0
    assert s.expand(D[1,2]+J.diff(x)+3*G.diff(x)/z)==0
    assert s.expand(D[0,1]+J.diff(T)+3*G.diff(T)/z)==0
    assert s.expand(D[0,0]-B+G.diff(T,2)-3*G.diff(z)/z+24*G/z**2+8*J/z)==0
    q=u-F/3; AJ=A(J)+J/z**2
    assert s.expand(L(q)-z*(B.diff(z)-AJ)/6+B/3-2*J/(3*z))==0
    assert s.expand(F.diff(z)-2*F/z-6*q/z-J)==0
    # Normal coordinate gauge shift in the scalar longitudinal chart.
    xi=s.Function('xi')(*X)
    assert s.expand((u-xi/z)-(F-3*xi/z)/3-q)==0
    # Independent scalar wave divergence identity.
    assert s.expand(z**3*((z**-3*q.diff(z)).diff(z)+z**-3*box(q))-L(q))==0
    print('9 exact sourced scalar master and constraint identities PASS')

if __name__=='__main__':exact()
