#!/usr/bin/env python3
"""BR96–99: original Hopf reflection audit and candidate F continuous
geometric gauge allocation. Classical wave transmission, trace energy,
Lorentz and KK geometry prior mathematics; DASHI-specific signed
source/row attachment. No actual nonlinear reduced existence claimed.
"""
import argparse
from itertools import combinations_with_replacement
import sympy as s
Q=s.Rational
def eq(a,b):
    assert (a-b).applyfunc(s.cancel)==s.zeros(*a.shape)

def br96():
    # Exact coordinate formula from original P0AN metric: use
    # rational derivatives at the origin, no JAX or interval claims.
    x=s.Matrix(s.symbols('x:3'));r=x.dot(x);h=Q(4,5);eps=s.Symbol('eps')
    fac=2*(1+r)/(h*(1-r)**2);X=fac*x
    pull=X.jacobian(x);X1,X2,X3=X
    A=2*s.Matrix([2*X1*X3-2*X2,2*X1+2*X2*X3,1-X1**2-X2**2+X3**2])/(1+X.dot(X))**2
    # Only first jets needed; use chain rule before expanding.
    origin=dict.fromkeys(x,0)
    a0=eps*pull.subs(origin)*A.subs(origin)
    da=eps*pull.subs(origin)*A.jacobian(x).subs(origin)
    da+=s.Matrix.hstack(*(eps*pull.diff(v).subs(origin)*A.subs(origin) for v in x))
    assert a0==s.Matrix([0,0,5*eps])
    assert da[1,0]-da[0,1]==50*eps
    assert (da[1,0]-da[0,1]).subs(eps,Q(1,40))==Q(5,4)
    # The KK readback g_an/g_nn is unchanged by scalar conformal
    # factor and BE/BO/BQ tangential-only corrections.
    a=s.Matrix(s.symbols('a:3'));u=s.Symbol('u',positive=True)
    P=s.Matrix(3,3,lambda i,j:s.Symbol(f'H{min(i,j)}{max(i,j)}'))
    B=P.row_join(a).col_join(a.T.row_join(s.ones(1)))
    g=u*u*B
    eq(g[:3,3]/g[3,3],a)
    # Normal reflection sends the KK ratio to -a. A base-identity
    # orientation reversal y'=L-y+f(x) would require df=-2a,
    # hence d a=0, contradicted by the original source.
    R=s.diag(1,1,1,-1)
    eq((R.T*g*R)[:3,3]/g[3,3],-a)
    # Combined signed amplitude relation is different from invariance.
    n,L=s.symbols('n L',positive=True);b=s.Function('b')
    f=n*n*(L-n)**2*(L-2*n)/L**3
    assert s.expand(f.subs(n,L-n)+f)==0
    print('PASS BR96 exact AN Hopf nonzero curvature dA_xy(0)=50 eps=5/4 at eps=1/40; pure normal reflection refused')
    print('BR96 qualification: fixed-base circle reflection only; not a no-go for all spacetime isometries')

def metric_F(p,px,m,mx,z,j):
    from check_hopf369_br_warped_physical_attachment import metric_rows,metric_side
    rows=metric_rows(p,px,m,mx,z,j,'D')
    rows[28]=metric_side(p,px,z,j/2)[5]-metric_side(m,mx,z,-j/2)[5]
    return rows

def gauge_F(p,px,m,mx,z,j):
    from check_hopf369_br_warped_physical_attachment import gauge_rows
    rows=gauge_rows(p,px,m,mx,z,j,'D')
    # Keep D order (normal first), change only one value row.
    rows[0]=p[4]-m[4]
    return rows

def principal_matrix(sector,z):
    from check_hopf369_br_full_warped_symbol import dec
    n=30 if sector=='metric' else 10
    def row(v):
        if sector=='metric':
            p,m=dec(v[:15,0]),dec(v[15:,0])
            return metric_F(p,-p,m,m,z,s.S.Zero)
        p,m=v[:5,0],v[5:,0]
        return gauge_F(p,-p,m,m,z,s.S.Zero)
    return s.Matrix.hstack(*(row(s.eye(n)[:,k]) for k in range(n)))

def br97(sector,ray):
    w=s.symbols('w',nonzero=True)
    z=s.Matrix([(w+1/w)/2,(w-1/w)/2,0,0]) if ray else s.Matrix([1,0,0,0])
    B=principal_matrix(sector,z);inv=B.inv(method='DM').applyfunc(s.cancel);n=B.rows
    eq(B*inv,s.eye(n));eq(inv*B,s.eye(n))
    if not ray:
        c=max(sum(abs(x) for x in inv.row(i)) for i in range(n))
        assert c=={'metric':8,'gauge':Q(3,2)}[sector]
        print('PASS BR97 F full rest principal inverse',sector,'norm',c)
        return
    powers=[];costs=[]
    for x in inv:
        if not x:costs.append(0);continue
        a,b=s.fraction(x);c,fs=s.factor_list(b,w)
        assert all(p==w for p,k in fs) # no E temporal pole
        powers.append(s.degree(a,w)-s.degree(b,w))
        costs.append(sum(abs(v) for v in s.Poly(a,w).all_coeffs())/abs(c))
    bound=max(sum(costs[i*n:(i+1)*n]) for i in range(n))
    assert max(powers)=={'metric':3,'gauge':1}[sector]
    assert bound=={'metric':11,'gauge':2}[sector]
    print('PASS BR97 F exact Laurent inverse',sector,'glancing exponent',max(powers),'bound',bound,'no opposite-sector pole')

def finite_flat():
    # BR33 reduced 20-row finite interval with independent T,C,
    # not just a half-space. F replaces plus normal with jump.
    z=s.Matrix(s.symbols('z:4'));h=s.diag(-1,1,1,1)
    T,C=s.symbols('T C',nonzero=True);q=(z.T*h*z)[0]
    div=lambda v:(z.T*h*v)[0]
    keys=list(combinations_with_replacement(range(4),2))
    hs=s.symbols('h:10');H=s.Matrix(4,4,lambda a,b:hs[keys.index(tuple(sorted((a,b))))])
    bp,bm=[s.Matrix(s.symbols(f'{k}:4')) for k in ('bp','bm')]
    lp,lm=s.symbols('lp lm');d=bp-bm;b=bp+bm;p=lp-lm;a=lp+lm
    J=-2*T*H-z*d.T-d*z.T;ct=-z*p-T*b;nn=T*s.trace(h*H)+div(d)-T*a
    rows=s.Matrix([J[i,j] for i,j in keys]+list(ct)+[nn]+list(d)+[-div(b)])
    v=s.Matrix([*hs,*bp,*bm,lp,lm]);B=rows.jacobian(v)
    r=s.Matrix(s.symbols('r:20'));d=r[15:19,0]
    JJ=s.Matrix(4,4,lambda i,j:r[keys.index(tuple(sorted((i,j))))])
    HH=-(JJ+z*d.T+d*z.T)/(2*T)
    pp=(T*r[19]-div(r[10:14,0]))/q
    bb=-(r[10:14,0]+z*pp)/T
    aa=s.trace(h*HH)+(div(d)-r[14])/T
    sol=s.Matrix([HH[i,j] for i,j in keys]+list((bb+d)/2)+list((bb-d)/2)+[(aa+pp)/2,(aa-pp)/2])
    eq(B*sol,r)
    det=s.factor(B.det(method='domain-ge'))
    assert s.cancel(det/(2**14*T**14*q)) in (1,-1)
    # F gauge finite interval: arbitrary jumps, derivatives, no z0.
    j=s.symbols('j');cp,cm=[s.Matrix(s.symbols(f'{k}:4')) for k in ('cp','cm')]
    u,vn=s.symbols('u vn');cg=cp-cm;cs=cp+cm;ng=u-vn;ns=u+vn
    G=s.Matrix([ng,*cg,*(-(T+j)*cs+z*ng),-(T+2*j)*ns-div(cg)])
    V=s.Matrix([*cp,*cm,u,vn]);F=s.Matrix(s.symbols('f:10'))
    gg=F[1:5,0];ng=F[0];ns=-(F[9]+div(gg))/(T+2*j)
    cs=(z*ng-F[5:9,0])/(T+j)
    out=s.Matrix([*((cs+gg)/2),*((cs-gg)/2),(ns+ng)/2,(ns-ng)/2])
    eq(G.jacobian(V)*out,F)
    print('PASS BR97 F finite interval arbitrary-forcing metric and gauge inverse; metric determinant',det)

def br98():
    # Genuine matched wall shape, arbitrary nonzero mean and common
    # covector C. Physical Gaussian coordinate derivative jump.
    h=s.diag(-1,1,1,1);j=s.symbols('j',real=True)
    M=s.Matrix(4,4,lambda a,b:s.Symbol(f'M{min(a,b)}{max(a,b)}'))
    M[0,0]=sum(M[i,i] for i in range(1,4))
    Kp=M+j*h/2;Km=M-j*h/2
    c=s.Matrix(s.symbols('c:4'));n=s.Symbol('n')
    dp,dm=[s.Matrix(s.symbols(f'{k}:5')) for k in ('dp','dm')]
    cod=dp[:4,0]-dm[:4,0]-2*(Kp-Km)*h*c
    gauss=dp[4]-dm[4]-(s.trace(h*Kp)-s.trace(h*Km))*n
    eq(cod,dp[:4,0]-dm[:4,0]-2*j*c)
    assert s.expand(gauss-(dp[4]-dm[4]-4*j*n))==0
    # In covariant normal parallel components connection subtracts
    # another j C_a; physical coordinate energy uses the former jump.
    eq((dp[:4,0]-Kp*h*c)-(dm[:4,0]-Km*h*c),dp[:4,0]-dm[:4,0]-j*c)
    # Common positive wall component Gram commutes with Robin split.
    G=s.diag(2,3,4,5,6);S=s.diag(*([2*j]*4+[4*j]))
    val=c.col_join(s.Matrix([n]));dt=s.Matrix(s.symbols('v:5'))
    assert G*S==(G*S).T
    flux=-(dt.T*G*S*val)[0]
    assert s.expand(flux+(dt.T*G*S*val+val.T*G*S*dt)[0]/2)==0
    # Variable positive weights: differentiate potential and retain
    # coefficient work instead of declaring exact total conservation.
    Gt=s.diag(*s.symbols('gt:5'))
    remain=s.expand(flux+((dt.T*G*S*val+val.T*G*S*dt+val.T*Gt*S*val)[0])/2)
    assert s.expand(remain-(val.T*Gt*S*val)[0]/2)==0
    print('PASS BR98 physical F Codazzi/Gauss derivative jumps, common positive boundary energy and Robin potential')

def br99():
    # Full actual BR34 rest warped perturbation bound. Relative
    # endpoint derivative error δ includes optical-to-parallel
    # conversion and finite-interval flat tails. Metric row norm
    # derivative coefficient <=5; explicit j lower row bound <=3|j|.
    # Gauge derivative row norm <=2; lower row bound <=4|j|.
    d,j,L=s.symbols('delta j L',positive=True)
    rhoM=8*(5*d+3*j/L);rhoG=Q(3,2)*(2*d+4*j/L)
    sub={d:Q(1,1000),j:Q(6,5),L:1000}
    assert rhoM.subs(sub)<Q(1,2) and rhoG.subs(sub)<Q(1,2)
    # Verify operator coefficient constants using actual F row builders.
    from check_hopf369_br_full_warped_symbol import dec
    for sector,boundD,boundJ in [('metric',5,3),('gauge',2,4)]:
        n=30 if sector=='metric' else 10;z=s.Matrix([1,0,0,0])
        def f(v,dv,j):
            if sector=='metric':return metric_F(dec(v[:15,0]),dec(dv[:15,0]),dec(v[15:,0]),dec(dv[15:,0]),z,j)
            return gauge_F(v[:5,0],dv[:5,0],v[5:,0],dv[5:,0],z,j)
        Z=s.zeros(n,1)
        P=s.Matrix.hstack(*(f(Z,s.eye(n)[:,i],0) for i in range(n)))
        J=s.Matrix.hstack(*(f(s.eye(n)[:,i],Z,1)-f(s.eye(n)[:,i],Z,0) for i in range(n)))
        assert max(sum(abs(x) for x in P.row(i)) for i in range(n))<=boundD
        assert max(sum(abs(x) for x in J.row(i)) for i in range(n))<=boundJ
    print('PASS BR99 actual F row perturbation factors; conditional BR35 rest DtN bound, not variable IBVP')

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=['reflection','rest','ray','finite','energy','warp'],required=True)
    p.add_argument('--sector',choices=['metric','gauge'],default='metric')
    a=p.parse_args()
    if a.part in ('rest','ray'):br97(a.sector,a.part=='ray')
    else:{'reflection':br96,'finite':finite_flat,'energy':br98,'warp':br99}[a.part]()
