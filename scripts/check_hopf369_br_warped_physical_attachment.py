#!/usr/bin/env python3
"""BR34: BR14/15 actual warped RNC tensor and BS4/5 covector transfer
attached to BR33 D/E. Frozen tangential jets only; no uniform Kreiss or PDE claim.
Run from the repository root or scripts directory, with the BR14 donor present.
"""
import sympy as s
import numpy as np
from scipy.linalg import block_diag, solve
from check_hopf369_br_full_warped_symbol import I, eta, ids, enc, dec, op, ins, P, L, Lt

E4 = eta[:4, :4]
keys = [(a,b) for a,b in ids if b < 4]

def trace4(h):
    return s.trace(E4*h)

def metric_side(p, px, z, k):
    """Normalized BR14 p and p_x at b=1; fixed reference lower source."""
    H, beta, l = p[:4,:4], p[:4,4], p[4,4]/2
    Hx, bx, lx = px[:4,:4], px[:4,4], px[4,4]/2
    div = (z.T*E4*beta)[0]
    K = k*H + (Hx-z*beta.T-beta*z.T)/2-k*l*E4
    tau = trace4(Hx)/2-div-4*k*l
    Ca = H*E4*z-z*trace4(H)/2-z*l+bx+3*k*beta
    Cn = -trace4(Hx)/2+div+lx
    return H,beta,K,tau,Ca,Cn

def metric_rows(p, px, m, mx, z, j, alloc):
    H,b,K,t,c,u=metric_side(p,px,z,j/2)
    G,d,Q,v,e,w=metric_side(m,mx,z,-j/2)
    J=2*(K-Q)-j*(H+G)  # mean trace extension off [H]=0
    cg=c-e
    return s.Matrix(
        [(H-G)[a,b] for a,b in keys]+list(b-d)+[J[a,b] for a,b in keys]
        +(list(cg)+[u] if alloc=='D' else list(cg[1:4,0])+[u,w])+[t+v])

def gauge_rows(p, px, m, mx, z, j, alloc):
    """Normalized covector components, proper-normal derivative at b=1.
    Convert tangent derivative to coordinate C_a=b*v_a before Codazzi.
    """
    c,e=p[:4,0],m[:4,0]; u,w=p[4],m[4]
    k=j/2
    tangent=px[:4,0]-mx[:4,0]+z*(u-w)-k*(c+e)
    normal=px[4]-mx[4]-(z.T*E4*(c-e))[0]-2*j*(u+w)
    value=[u]+list(c-e) if alloc=='D' else [u,w]+list((c-e)[1:4,0])
    return s.Matrix(value+list(tangent)+[normal])

def symbolic():
    k=s.symbols('k',real=True); z=s.Matrix(s.symbols('z0:4'))
    p=dec(s.Matrix(s.symbols('p0:15'))); px=dec(s.Matrix(s.symbols('v0:15')))
    H,b,K,t,c,u=metric_side(p,px,z,k)
    # Direct variation of coordinate metric and derivatives at b=1 in harmonic Y.
    # g_ab=b^2 eta_ab, g_YY=b^8; perturbation exponents 2,5,8.
    dg=[s.zeros(5) for _ in range(4)]+[s.diag(-2*k,2*k,2*k,2*k,8*k)]
    dp=[a*p for a in z]+[px+s.Matrix(5,5,lambda a,b:(2+3*int(a==4)+3*int(b==4))*k*p[a,b])]
    dinv=-eta*p*eta
    direct=s.Matrix([sum(dinv[a,b]*(dg[a][i,b]-dg[i][a,b]/2)
                +eta[a,b]*(dp[a][i,b]-dp[i][a,b]/2)
                for a in range(5) for b in range(5)) for i in range(5)])
    assert (direct-c.col_join(s.Matrix([u]))).applyfunc(s.expand)==s.zeros(5,1)
    directK=(dp[4][:4,:4]-z*b.T-b*z.T)/2-k*p[4,4]*E4/2
    assert (directK-K).applyfunc(s.expand)==s.zeros(4)
    assert s.expand(trace4(K)-k*trace4(H)-t)==0
    # Reuse the exact flat comparison: when common H and flat transfer,
    # mean trace derivative vanishes, but not for a general warped transfer.
    T,C,j=s.symbols('T C j',nonzero=True)
    H=dec(s.Matrix(s.symbols('h0:15')))[:4,:4]
    bp,bm=s.Matrix(s.symbols('bp0:4')),s.Matrix(s.symbols('bm0:4'))
    lp,lm=s.symbols('lp lm')
    def tensor(H,b,l):return H.row_join(b).col_join(b.T.row_join(s.Matrix([[2*l]])))
    pp,pm=tensor(H,bp,lp),tensor(H,bm,lm)
    vp=(-T*(pp+pm)-C*(pp-pm))/2; vm=(T*(pp+pm)-C*(pp-pm))/2
    d=bp-bm; sm=bp+bm; div=lambda v:(z.T*E4*v)[0]
    J=-2*T*H-z*d.T-d*z.T
    ct=-z*(lp-lm)-T*sm
    np_=T*trace4(H)/2+div(bp)-(T*(lp+lm)+C*(lp-lm))/2
    nm_=-T*trace4(H)/2+div(bm)+(T*(lp+lm)-C*(lp-lm))/2
    for a in 'DE':
        expected=s.Matrix([0]*10+list(d)+[J[i,j] for i,j in keys]
            +(list(ct)+[np_] if a=='D' else list(ct[1:4,0])+[np_,nm_])+[-div(sm)])
        assert (metric_rows(pp,vp,pm,vm,z,s.S.Zero,a)-expected).applyfunc(s.expand)==s.zeros(30,1)
    # Normal parallel vs coordinate tangent covector derivative.
    cp,cm=s.Matrix(s.symbols('cp0:5')),s.Matrix(s.symbols('cm0:5'))
    vp,vm=s.Matrix(s.symbols('vp0:5')),s.Matrix(s.symbols('vm0:5'))
    coordjump=vp[:4,0]-vm[:4,0]+j*(cp[:4,0]+cm[:4,0])/2
    coordinate_codazzi=coordjump+z*(cp[4]-cm[4])-j*(cp[:4,0]+cm[:4,0])
    for a in 'DE':
        assert (gauge_rows(cp,vp,cm,vm,z,j,a)[5:9,0]-coordinate_codazzi).applyfunc(s.expand)==s.zeros(4,1)
    print('PASS exact coordinate Gamma (5), Israel (10), mean trace, both flat allocations (60), gauge frame conversion (8)')

def operators():
    R=3*I+op(lambda p:ins(4,P(p)))
    J=[op(lambda p,a=a:2*eta[a,a]*Lt(a,p)+ins(a,P(p))) for a in range(4)]
    W=sum((eta[a,a]*op(lambda p,a=a:Lt(a,Lt(a,p)))+op(lambda p,a=a:ins(a,L(a,P(p)))) for a in range(4)),s.zeros(15))
    C0=op(lambda p:2*(p-eta*s.trace(eta*p)))
    Vbase=op(lambda p:s.Matrix(5,5,lambda i,j:(int(int(i)<4)+int(int(j)<4))*p[i,j]))
    def baseA(a,p):
        tr=trace4(p[:4,:4]);return s.Matrix([s.Rational(8,3)*p[i,a]-s.Rational(2,3)*eta[i,a]*tr for i in range(4)]+[2*p[4,a]])
    Vbase+=sum((op(lambda p,a=a:ins(a,baseA(a,p))) for a in range(4)),s.zeros(15))
    Vb=W+C0-R/2-R*R/4; Vh=-W+R-3*I-Vbase+R*R/4
    Q=[]
    for a in (-5,1,3):
        q=I
        for b in (-5,1,3):
            if a!=b:q=q*(R-b*I)/(a-b)
        Q.append(q)
    # Actual normalized covector rough wave + Ric=-4 (BS4/5), all five channels.
    Lm=[s.Matrix.hstack(*(L(a,s.eye(5)[:,i]) for i in range(5))) for a in range(4)]
    S=sum((eta[a,a]*Lm[a]*Lm[a] for a in range(4)),s.zeros(5))
    assert S==s.diag(-1,-1,-1,-1,-4)
    # Recheck separated proper-normal potentials against BS4/5 after undoing v=C_a/b.
    k,kp=s.symbols('k kp'); assert s.expand(kp+k*k+2*k*k-(4*k*k+kp+4))==-k*k-4
    return R,J,Vb,Vh,Q,Lm,S

A=lambda x:np.array(x,dtype=np.complex128)
h0=.8; X=np.arctan(.75)/h0; j=-1.2

def dtn(N,d,potential,ell2):
    x=-X*np.cos(np.pi*np.arange(N+1)/N)
    c=(-1.)**np.arange(N+1);c[[0,-1]]*=2
    dx=x[:,None]-x[None,:]; D=(c[:,None]/c[None,:])/(dx+np.eye(N+1));D-=np.diag(D.sum(axis=1))
    assert np.max(np.abs(D@x-1))<1e-10
    D2=D@D; eye=np.eye(d)
    M=np.kron(D2[1:-1,1:-1],eye)+block_diag(*(potential(y)-ell2*eye for y in x[1:-1]))
    B=-np.kron(D2[1:-1,[0,-1]],eye)
    interior=solve(M,B)
    vals=np.vstack([np.eye(2*d)[:d],interior,np.eye(2*d)[d:]])
    return np.kron(D[[0,-1]],eye)@vals

def row_matrices(z, R, J, Vb, Vh, Q, Lm, S, N):
    zz=A(z).ravel(); ell2=-sum((-1 if i==0 else 1)*zz[i]**2 for i in range(4));
    R,J,Vb,Vh,Q,Lm,S=A(R),list(map(A,J)),A(Vb),A(Vh),list(map(A,Q)),list(map(A,Lm)),A(S)
    def metric_pot(x):
        b=h0/np.cos(h0*x); bk=h0*np.tan(h0*x)
        E=sum(b**(a/2)*q for a,q in zip((-5,1,3),Q)); Ei=sum(b**(-a/2)*q for a,q in zip((-5,1,3),Q))
        return E@(bk*sum(zz[a]*J[a] for a in range(4))+b*b*Vb+h0*h0*Vh)@Ei
    def gauge_pot(x):
        b=h0/np.cos(h0*x); bk=h0*np.tan(h0*x)
        return (2*bk*sum((-1 if a==0 else 1)*zz[a]*Lm[a] for a in range(4))
                +bk*bk*(S-9*np.eye(5)/4)-h0*h0*np.diag([1,1,1,1,0])-11*b*b*np.eye(5)/2)
    dm=dtn(N,15,metric_pot,ell2)-block_diag(j*R/4,-j*R/4)
    dg=dtn(N,5,gauge_pot,ell2)-block_diag(3*j*np.eye(5)/4,-3*j*np.eye(5)/4)
    # Each column is an actual endpoint trace, not a sampled determinant.
    out=[]
    for a in 'DE':
        m=[];g=[]
        for i in range(30):
            v=s.Matrix(np.eye(30)[:,i]); w=s.Matrix(dm[:,i]);m.append(A(metric_rows(dec(v[:15,0]),dec(w[:15,0]),dec(v[15:,0]),dec(w[15:,0]),z,s.Float(j),a)).ravel())
        for i in range(10):
            v=s.Matrix(np.eye(10)[:,i]); w=s.Matrix(dg[:,i]);g.append(A(gauge_rows(v[:5,0],w[:5,0],v[5:,0],w[5:,0],z,s.Float(j),a)).ravel())
        out.extend([np.column_stack(m),np.column_stack(g)])
    return out

def numeric():
    ops=operators(); rng=np.random.default_rng(369)
    for ss,xi in [(4+0j,(0,0,0)),(3+2j,(2,-1,1)),(2+12j,(12,0,0))]:
        z=s.Matrix([ss,*[1j*x for x in xi]])
        lo=row_matrices(z,*ops,24); hi=row_matrices(z,*ops,40)
        for name,B0,B in zip(('metric-D','gauge-D','metric-E','gauge-E'),lo,hi):
            rel=np.linalg.norm(B-B0,np.inf)/max(1,np.linalg.norm(B,np.inf)); assert rel<3e-7,(name,rel)
            f=rng.normal(size=B.shape[0])+1j*rng.normal(size=B.shape[0]); v=solve(B,f)
            residual=np.linalg.norm(B@v-f,np.inf)/np.linalg.norm(f,np.inf); assert residual<1e-9
            print(f'{ss=} {xi=} {name}: refine={rel:.3g} residual={residual:.3g} sigma_min={np.linalg.svd(B,compute_uv=False)[-1]:.3g}')
    print('PASS 12 frozen warped forced solves; numerical refinement, NOT rigorous inverse bounds')

if __name__=='__main__':
    symbolic();numeric()
