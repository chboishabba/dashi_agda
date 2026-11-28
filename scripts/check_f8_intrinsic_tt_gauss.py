"""Quadratic intrinsic FRW TT scalar curvature, independent of bulk equations.
Exact local jets; consumes original spatial TT field, not a new source.
"""
import sympy as s
from itertools import product

def exact():
    t,x,y,z=s.symbols('t x y z',positive=True); coords=(t,x,y,z); b=1/t
    # Nonparallel transverse waves, with noncommuting polarizations.
    H=s.Matrix([[0,0,t*y],[0,t*x+t*t,0],[t*y,0,-t*x-t*t]])
    # H_xx must cancel transverse divergence: H_xz independent z and x.
    assert s.trace(H)==0
    assert all(sum(H[i,j].diff(coords[i+1]) for i in range(3))==0 for j in range(3))
    g=s.diag(-1,t*t*s.eye(3)); h=s.diag(0,t*t*H); gi=g.inv(); di=-gi*h*gi; ddi=gi*h*gi*h*gi
    I=range(4); zero=s.zeros(4)
    def conn(inv,metric):
        return [s.Matrix(4,4,lambda a,c:s.expand(sum(inv[a,k]*(metric[k,c].diff(coords[m])+metric[k,m].diff(coords[c])-metric[m,c].diff(coords[k]))/2 for k in I))) for m in I]
    C0=conn(gi,g); A=conn(gi,h); B=conn(di,g); C1=[a+b for a,b in zip(A,B)]; A=conn(di,h); B=conn(ddi,g); C2=[a+b for a,b in zip(A,B)]
    C=[C0,C1,C2]
    def ric(n):
        return s.Matrix(4,4,lambda i,j:s.expand(sum(C[n][i][k,j].diff(coords[k])-C[n][i][k,k].diff(coords[j]) for k in I)+sum(sum((C[a][k]*C[n-a][i]-C[a][i]*C[n-a][k])[k,j] for a in range(n+1)) for k in I)))
    # Standard Ricci: R_ij=∂k Γ^k_ij-∂j Γ^k_ik+Γ^k_kl Γ^l_ij-Γ^k_jl Γ^l_ik.
    R0,R1,R2=[ric(n) for n in range(3)]
    actual=s.expand(s.trace(gi*R2+di*R1+ddi*R0))
    # Independent ADM time part: 2 ∂t trK + (trK)^2 + tr(K²), K= bI+epsilon Ht/2-epsilon² H Ht/2.
    K0=b*s.eye(3); K1=H.diff(t)/2; K2=-H*H.diff(t)/2
    time=s.expand(2*s.trace(K2).diff(t)+2*s.trace(K0)*s.trace(K2)+s.trace(K1*K1+2*K0*K2))
    assert s.expand(time+s.trace(H*H.diff(t,2))+s.Rational(3,4)*s.trace(H.diff(t)**2)+4*b*s.trace(H*H.diff(t)))==0
    # Independent spatial Christoffel expansion, TT spatial scalar at quadratic order.
    X=coords[1:]; ix=range(3)
    G=[s.Matrix(3,3,lambda a,c:(H[a,c].diff(X[m])+H[a,m].diff(X[c])-H[m,c].diff(X[a]))/2) for m in ix]
    D=[-H*A for A in G]
    r1=s.Matrix(3,3,lambda i,j:sum(G[i][k,j].diff(X[k])-G[i][k,k].diff(X[j]) for k in ix))
    r2=s.Matrix(3,3,lambda i,j:sum(D[i][k,j].diff(X[k])-D[i][k,k].diff(X[j])+(G[k]*G[i]-G[i]*G[k])[k,j] for k in ix))
    spatial=s.expand(s.trace(r2-H*r1))
    assert s.expand(actual-time-b*b*spatial)==0,(actual,time,spatial)
    assert actual!=0 and spatial!=0
    print('6 exact assertions PASS; intrinsic FRW quadratic TT curvature, independent ADM/spatial split')
    print('sample quadratic scalar:',actual)
if __name__=='__main__':exact()
