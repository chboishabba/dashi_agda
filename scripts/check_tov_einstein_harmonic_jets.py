#!/usr/bin/env python3
"""Exact local Einstein--matter jets for the repaired TOV source.
Interior linear operator, affine metric Hessian, harmonic/gauge diagnostics.
No moving-domain GHY Hessian, global constraint inverse or stability claim.
"""
import argparse
from itertools import product
import sympy as s

I=range(4); J=list(product(I,repeat=3)); Z4=lambda:s.zeros(4)

def fields(M,x,point):
    ev=lambda A:A.subs(point).applyfunc(s.simplify)
    return ev(M),[ev(M.diff(a)) for a in x],[[ev(M.diff(a,b)) for b in x] for a in x]

def curvature(base,pert=None,order=1):
    """Ordinary epsilon coefficients, not factorial-normalized derivatives.
    Input (g, partial g, partial^2 g), and affine perturbation jets.
    Output inverse, Ricci, Einstein, scalar curvature and connection jets.
    """
    g,dg,ddg=base
    h,dh,ddh=pert if pert is not None else (Z4(),[Z4() for _ in I],[[Z4() for _ in I] for _ in I])
    clean=lambda M:M.applyfunc(s.cancel)
    G=[g.inv()]
    for n in range(1,order+1):G.append(clean(-G[n-1]*h*G[0]))
    gs=[g,h]+[Z4()]; ds=[dg,dh]+[[Z4() for _ in I]]; dds=[ddg,ddh]+[[[Z4() for _ in I] for _ in I]]
    dG=[[clean(-sum((G[i]*ds[j][k]*G[n-i-j] for i in range(n+1) for j in range(n-i+1)),Z4())) for k in I] for n in range(order+1)]
    def lower(n,a,b,c):return (ds[n][b][a,c]+ds[n][c][a,b]-ds[n][a][b,c])/2
    def dlower(n,k,a,b,c):return (dds[n][k][b][a,c]+dds[n][k][c][a,b]-dds[n][k][a][b,c])/2
    C=[]; dC=[]
    for n in range(order+1):
        C.append({(a,b,c):s.cancel(sum(G[i][a,d]*lower(n-i,d,b,c) for i in range(n+1) for d in I)) for a,b,c in J})
        dC.append({(k,a,b,c):s.cancel(sum(dG[i][k][a,d]*lower(n-i,d,b,c)+G[i][a,d]*dlower(n-i,k,d,b,c) for i in range(n+1) for d in I)) for k in I for a,b,c in J})
    R=[]; S=[]; E=[]
    for n in range(order+1):
        R.append(clean(s.Matrix(4,4,lambda b,c:sum(dC[n][a,a,b,c]-dC[n][c,a,b,a]+sum(C[i][a,a,d]*C[n-i][d,b,c]-C[i][a,c,d]*C[n-i][d,b,a] for d in I for i in range(n+1)) for a in I))))
        S.append(s.cancel(sum(s.trace(G[i]*R[n-i]) for i in range(n+1))))
        E.append(clean(R[n]-sum((gs[i]*S[n-i]/2 for i in range(n+1)),Z4())))
    return G,R,E,S,C,dC

def eh(base,pert):
    g=base[0]; h=pert[0]; G,R,E,S,C,dC=curvature(base,pert,2)
    H=G[0]*h; j1=s.trace(H)/2; j2=s.trace(H)**2/4-s.trace(H*H)/2
    # Affine path second derivative of sqrt(-g) R, divided by sqrt(-g0).
    return s.cancel(2*S[2]+2*j1*S[1]+j2*S[0]),(G,R,E,S,C,dC)

def curvature_test():
    t,x,y,z=s.symbols('t x y z',real=True); X=(t,x,y,z); point=dict.fromkeys(X,0)
    g=s.diag(-1,1,s.exp(2*x),1)
    h=s.Matrix([[-x-t*x,y+s.Rational(1,7),0,0],[y+s.Rational(1,7),x*x+z,0,0],[0,0,x*y+t+s.Rational(1,11),0],[0,0,0,z*z+x]])
    base=fields(g,X,point); pert=fields(h,X,point)
    val,(G,R,E,S,C,dC)=eh(base,pert)
    # Covariant connection-difference identity; independent of coordinate
    # Ricci product expansion. C[2] is half of the second variation.
    hh=G[0]*pert[0]
    for a,b,c in J:
        assert C[2][a,b,c]==-sum(hh[a,d]*C[1][d,b,c] for d in I)
    def cov(n,k,a,b,c):
        return dC[n][k,a,b,c]+sum(C[0][a,k,d]*C[n][d,b,c]-C[0][d,k,b]*C[n][a,d,c]-C[0][d,k,c]*C[n][a,b,d] for d in I)
    for b,c in product(I,repeat=2):
        for n in (1,2):
            q=sum(cov(n,a,a,b,c)-cov(n,c,a,b,a) for a in I)
            if n==2:q+=sum(C[1][a,a,d]*C[1][d,b,c]-C[1][a,c,d]*C[1][d,b,a] for a,d in product(I,repeat=2))
            assert s.cancel(q-R[n][b,c])==0
    # Exact affine metric at the point, no epsilon truncation in oracle.
    e=s.symbols('e',real=True); g0,dg,ddg=base; h0,dh,ddh=pert
    exact=(g0+e*h0,[dg[k]+e*dh[k] for k in I],[[ddg[k][l]+e*ddh[k][l] for l in I] for k in I])
    _,re,_,se,_,_=curvature(exact,order=0)
    for n in (1,2):assert (re[0].diff(e,n).subs(e,0)-s.factorial(n)*R[n]).applyfunc(s.cancel)==Z4()
    density=s.sqrt(exact[0].det()/g0.det())*se[0]
    assert s.simplify(density.diff(e,2).subs(e,0)-val)==0
    # Independent four-dimensional conformal transformation oracle.
    phi=1+t+2*x+3*y+z*z
    ch=fields(phi*g,X,point); value,_=eh(base,ch)
    grad=s.Matrix([s.diff(phi,k).subs(point) for k in X])
    assert s.cancel(value-3*(grad.T*G[0]*grad)[0])==0
    # Boundary current first variation: R1= -R^ab h_ab+div(V).
    v=[sum(G[0][b,c]*C[1][a,b,c]-G[0][a,b]*C[1][c,b,c] for b,c in product(I,repeat=2)) for a in I]
    dginv=[-G[0]*dg[k]*G[0] for k in I]
    div=sum(sum(dginv[a][b,c]*C[1][a,b,c]+G[0][b,c]*dC[1][a,a,b,c]-dginv[a][a,b]*C[1][c,b,c]-G[0][a,b]*dC[1][a,c,b,c] for b,c in product(I,repeat=2))+sum(C[0][a,a,b]*v[b] for b in I) for a in I)
    assert s.cancel(S[1]-s.trace(G[1]*R[0])-div)==0
    # Differentiated EH boundary current on the affine path. The connection
    # derivative is C1+2 epsilon C2; keep volume variation of the current.
    j1=s.trace(hh)/2
    G10=[-(dginv[k]*h0*G[0]+G[0]*dh[k]*G[0]+G[0]*h0*dginv[k]) for k in I]
    dj1=[s.trace(dginv[k]*h0+G[0]*dh[k])/2 for k in I]
    def cur(A,T,a):
        return sum(A[b,c]*T[a,b,c]-A[a,b]*T[c,b,c] for b,c in product(I,repeat=2))
    def dc(A,dA,T,dT,a):
        return sum(dA[b,c]*T[a,b,c]+A[b,c]*dT[a,a,b,c]-dA[a,b]*T[c,b,c]-A[a,b]*dT[a,c,b,c] for b,c in product(I,repeat=2))
    V1=[cur(G[1],C[1],a)+2*cur(G[0],C[2],a)+j1*v[a] for a in I]
    div1=sum(dc(G[1],G10[a],C[1],dC[1],a)+2*dc(G[0],dginv[a],C[2],dC[2],a)+dj1[a]*v[a]+j1*dc(G[0],dginv[a],C[1],dC[1],a)+sum(C[0][a,a,b]*V1[b] for b in I) for a in I)
    bulk=-s.trace(h0*(G[1]*E[0]*G[0]+G[0]*E[1]*G[0]+G[0]*E[0]*G[1]+j1*G[0]*E[0]*G[0]))
    assert s.cancel(val-bulk-div1)==0
    print('PASS curved Ricci/EH second jet, affine and conformal oracles, connection difference and first/second boundary currents',flush=True)


def tov(r0):
    t,r,th,ph=s.symbols('t r theta phi',real=True); x=(t,r,th,ph)
    point={t:0,r:r0,th:s.acos(s.Rational(4,5)),ph:0}
    ss=s.symbols('s',positive=True); lam=s.Rational(1,10); p=lam/(8*s.pi)
    rho=(2+lam)*p*(1-ss); pr=-p*(1-ss)**2
    f=1-lam*(2+lam)*(ss/3-ss**2/5)
    P=(2+lam)*(s.Rational(1,3)-ss/5)/2-(1-ss)**2/2
    pt=s.factor(pr+ss*s.diff(pr,ss)+ss*lam*(rho+pr)*P/(2*f))
    a=(rho+pt)/2; d=(rho+pr)/(2*f); b=s.cancel((d-a)/ss); V=rho-2*a-d*f; c=p*(1-ss)/2
    fr=f.subs(ss,r*r); nu=r*lam*P.subs(ss,r*r)/fr
    # Local lapse Taylor to third order, sufficient for pure gauge jets.
    n0,n1,n2=[s.diff(nu,r,k).subs(r,r0) for k in range(3)]
    dr=r-r0; N2=1+2*n0*dr+(n1+2*n0*n0)*dr**2+(n2/3+2*n0*n1+4*n0**3/3)*dr**3
    g=s.diag(-N2,1/fr,r*r,r*r*s.sin(th)**2)
    Y=r*s.Matrix([s.sin(th)*s.cos(ph),s.sin(th)*s.sin(ph),s.cos(th)])
    coeff=(ss,a,b,V,c,f)
    return x,point,g,Y,coeff


def stress(base,h,Y,A,Z,D,coeff):
    """Exact original target derivative and linearized covariant stress."""
    ss,a,b,V,c,f=coeff; s0=Y.dot(Y); ds=2*Y.dot(Z)
    ev=lambda q:s.cancel(q.subs(ss,s0)); I3=s.eye(3)
    K=ev(a)*I3+ev(b)*Y*Y.T
    K1=ev(s.diff(a,ss))*ds*I3+ev(s.diff(b,ss))*ds*Y*Y.T+ev(b)*(Z*Y.T+Y*Z.T)
    g=base; G=g.inv(); B=A*G*A.T
    B1=D*G*A.T+A*G*D.T-A*G*h*G*A.T
    B0=I3+(ev(f)-1)*Y*Y.T/s0
    B01=ev(s.diff(f,ss))*ds*Y*Y.T/s0+(ev(f)-1)*((Z*Y.T+Y*Z.T)/s0-Y*Y.T*ds/s0**2)
    assert (B-B0).applyfunc(s.cancel)==s.zeros(3)
    C=B.inv()*(B1-B01)
    Kb1=K1+ev(c)*(s.trace(C)*B.inv()-C*B.inv())
    W=s.trace(K*B)+ev(V); W1=s.trace(K1*B+K*B1)+ev(s.diff(V,ss))*ds
    T=2*A.T*K*A-g*W
    T1=2*(D.T*K*A+A.T*K*D+A.T*Kb1*A)-h*W-g*W1
    return T.applyfunc(s.cancel),T1.applyfunc(s.cancel)


def harmonic_test():
    for r0 in (s.Rational(1,2),s.Rational(3,4)):
        x,point,g,Y,coeff=tov(r0); t,r,th,ph=x
        base=fields(g,x,point); y0=Y.subs(point); A=Y.jacobian(x).subs(point)
        T,_=stress(base[0],Z4(),y0,A,s.zeros(3,1),s.zeros(3,4),coeff)
        E=curvature(base,order=0)[2][0]
        assert (E-8*s.pi*T).applyfunc(s.cancel)==Z4()
        def residual(h,z):
            hp=fields(h,x,point); zp=z.subs(point); D=z.jacobian(x).subs(point)
            _,T1=stress(base[0],hp[0],y0,A,zp,D,coeff)
            return (curvature(base,hp,1)[2][1]-8*s.pi*T1).applyfunc(s.cancel)
        for ell in (0,1,2,3):
            L=ell*(ell+1); H=s.legendre(ell,s.cos(th)); dH=s.diff(H,th)
            # Pure gauge with radial/time, polar and axial components.
            xi=s.Matrix([(1+t+r*r)*H,(r+t*r)*H,(1+r*t)*dH,(t+r*r)*dH/s.sin(th)])
            Xd=xi.jacobian(x); hg=sum((xi[k]*g.diff(x[k]) for k in I),Z4())+Xd.T*g+g*Xd
            zg=Y.jacobian(x)*xi
            assert residual(hg,zg)==Z4(),('gauge',r0,ell)
            if r0!=s.Rational(1,2):continue
            # All axisymmetric polar metric components, including trace-free
            # tensor harmonic, and material radial/polar displacement.
            tf=s.diff(H,th,2)+L*H/2
            hp=Z4(); hp[0,0]=(t+r*r)*H; hp[0,1]=hp[1,0]=(1+t*r)*H; hp[1,1]=(r+t*t)*H
            hp[0,2]=hp[2,0]=(t+r)*dH; hp[1,2]=hp[2,1]=(1+r*r)*dH
            hp[2,2]=r*r*((t+r)*H+(1+t*r)*tf)
            hp[3,3]=r*r*s.sin(th)**2*((t+r)*H-(1+t*r)*tf)
            zp=(r+t*r)*H*Y/r+(1+t*r)*dH*Y.diff(th)/r
            ep=residual(hp,zp)
            assert all(ep[i,3]==0 for i in range(3)) and ep!=Z4()
            if ell:
                ha=Z4(); Sphi=s.sin(th)*dH; Stp=(s.diff(Sphi,th)-2*s.cot(th)*Sphi)/2
                ha[0,3]=ha[3,0]=(t+r*r)*Sphi; ha[1,3]=ha[3,1]=(1+t*r)*Sphi
                ha[2,3]=ha[3,2]=(r+t*t)*Stp
                za=(1+t*r)*dH/s.sin(th)*Y.diff(ph)/r
                ea=residual(ha,za)
                assert all(ea[i,j]==0 for i,j in product(I,repeat=2) if (i==3)==(j==3)) and ea!=Z4()
            print('PASS original TOV gauge and parity mode',ell,flush=True)
    print('PASS original background and 8 curved pure-gauge modes; polar/axial residual separation',flush=True)


def boundary_test():
    # Coordinate radial graph at s(Y)=1, arbitrary angular/time dependence.
    # Material Lagrangian vanishes there for smooth finite strain. Its
    # first moving variation vanishes; its second endpoint term is -phi² L_r.
    r,e,phi,psi,Lr,L1,L2=s.symbols('r e phi psi Lr L1 L2',real=True)
    rb=1+e*phi+e**2*psi/2
    L=Lr*(r-1)+e*L1+e**2*L2/2
    edge=s.integrate(L,(r,1,rb))
    assert s.expand(edge).coeff(e,2)*2==2*phi*L1+phi**2*Lr
    assert s.expand(edge.subs(L1,-phi*Lr)).coeff(e,2)*2==-phi**2*Lr
    # At original TOV surface sqrt(-g)=j r² sin(theta), j(1)=1
    # (asymptotically normalized time). L=-sqrt(-g)*rho.
    lam,p,th=s.symbols('lambda p theta',positive=True)
    rho=(2+lam)*p*(1-r*r)
    Lbg=-r*r*s.sin(th)*rho
    assert s.simplify(s.diff(Lbg,r).subs(r,1)-2*(2+lam)*p*s.sin(th))==0
    print('PASS nonspherical moving material-domain endpoint term and original source surface slope',flush=True)


def constraints_test():
    x,point,g,Y,coeff=tov(s.Rational(1,2)); base=fields(g,x,point)
    nonzero=0
    for a in I:
        for b in range(a,4):
            h=Z4(); dh=[Z4() for _ in I]; ddh=[[Z4() for _ in I] for _ in I]
            ddh[0][0][a,b]=ddh[0][0][b,a]=1
            E=curvature(base,(h,dh,ddh),1)[2][1]
            assert E[0,:]==s.zeros(1,4)
            nonzero+=int(E!=Z4())
    assert nonzero==6
    print('PASS 10 independent second-time metric jets absent in Hamiltonian/momentum rows; 6 spatial evolution jets retained',flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--part',choices=['curvature','harmonics','constraints','boundary','all'],default='all'); part=p.parse_args().part
    for name,fn in [('curvature',curvature_test),('harmonics',harmonic_test),('constraints',constraints_test),('boundary',boundary_test)]:
        if part in (name,'all'):fn()
    print('OPEN moving-domain/GHY second variation, harmonic constraint inversion, radiative matching and stability')
