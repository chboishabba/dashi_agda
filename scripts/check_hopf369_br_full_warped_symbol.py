#!/usr/bin/env python3
"""Actual AK warped 15-component reduced symbol, frozen tangential RNC jets.
No variable-tangential-coefficient or nonlinear existence claim.
"""
import sympy as s
from itertools import combinations_with_replacement

D=5; n=4; eta=s.diag(-1,1,1,1,1); ids=list(combinations_with_replacement(range(D),2)); I=s.eye(15)
def enc(p):return s.Matrix([p[i,j] for i,j in ids])
def dec(v):return s.Matrix(D,D,lambda i,j:v[ids.index(tuple(sorted((i,j))))])
def op(f):return s.Matrix.hstack(*(enc(f(dec(I[:,i]))) for i in range(15)))
def cop(f):return s.Matrix.hstack(*(f(dec(I[:,i])) for i in range(15)))
def ins(a,v):
    e=s.eye(D)[:,a]; return e*v.T+v*e.T

def P(p):return s.Matrix([-2*p[a,n] for a in range(4)]+[s.trace(eta[:4,:4]*p[:4,:4])-4*p[n,n]])
def L(a,v):
    w=s.zeros(D,1); w[n]=-v[a]; w[a]=eta[a,a]*v[n];return w

def Lt(a,p):
    C=s.Matrix.hstack(*(L(a,s.eye(D)[:,i]) for i in range(D)));return C*p+p*C.T

def norm(A):return max(sum(abs(x) for x in A.row(i)) for i in range(A.rows))

def derive():
    R=3*I+op(lambda p:ins(n,P(p)))
    assert (R+5*I)*(R-I)*(R-3*I)==s.zeros(15)
    projectors=[]
    for a in [-5,1,3]:
        Q=I
        for b in [-5,1,3]:
            if a!=b:Q=Q*(R-b*I)/(a-b)
        assert Q*Q==Q and R*Q==a*Q
        projectors.append(Q)
    assert sum(projectors,s.zeros(15))==I
    J=[op(lambda p,a=a:2*eta[a,a]*Lt(a,p)+ins(a,P(p))) for a in range(4)]
    Vwarp=sum((eta[a,a]*op(lambda p,a=a:Lt(a,Lt(a,p)))+op(lambda p,a=a:ins(a,L(a,P(p)))) for a in range(4)),s.zeros(15))
    Vcurv=op(lambda p:2*(p-eta*s.trace(eta*p)))
    Vnormal=R-3*I
    # Base coordinate normal jets, sectional curvature K=-h0^2.
    # -sum eta^aa d_a Gamma^d_ab = K delta^d_b.
    Vbase=op(lambda p:s.Matrix(D,D,lambda i,j:(int(int(i)<n)+int(int(j)<n))*p[i,j]))
    def baseA(a,p):
        tr=s.trace(eta[:4,:4]*p[:4,:4]);return s.Matrix([s.Rational(8,3)*p[i,a]-s.Rational(2,3)*eta[i,a]*tr for i in range(4)]+[2*p[n,a]])
    Vbase+=sum((op(lambda p,a=a:ins(a,baseA(a,p))) for a in range(4)),s.zeros(15))
    # Verify base Christoffel jets independently from the RNC metric quadratic.
    x=s.Matrix(s.symbols('x0:4')); E=eta[:4,:4]; xx=E*x; q=(x.T*E*x)[0]
    h=E-(q*E-xx*xx.T)/3; zero=dict.fromkeys(x,0)
    dG={}
    for a,b,c,d in __import__('itertools').product(range(4),repeat=4):
        v=sum(E[a,l]*(s.diff(h[l,c],x[b],x[d])+s.diff(h[l,b],x[c],x[d])-s.diff(h[b,c],x[l],x[d]))/2 for l in range(4))
        dG[a,b,c,d]=v
        expected=-(int(a==c)*E[b,d]+int(a==b)*E[c,d]-2*E[b,c]*int(a==d))/3
        assert v==expected
    for b,d in __import__('itertools').product(range(4),repeat=2):
        assert -sum(E[a,a]*dG[d,a,b,a] for a in range(4))==int(b==d)
    # Optical x, u=b^(R/2)p. R constant, (log b)_x=b_n, (log b)_xx=b^2.
    # u_xx-ell²u + E [bk sum J_a zeta_a + V0] E^-1 u=0.
    h2=s.Rational(16,25)
    Vb=Vwarp+Vcurv-R/2-R*R/4
    Vh=-Vwarp+Vnormal-Vbase+R*R/4
    # Bound conjugation using projectors, b in [4/5,1], |b^±lambda/2|<2.
    cond=(2*sum(norm(Q) for Q in projectors))**2
    c1=cond*sum(norm(A) for A in J) # |bk|<=1; max |zeta_a|<=|zeta|
    c0=cond*(norm(Vb)+h2*norm(Vh))
    # Check exact coordinate-to-frame moving seam conversion from BR9.
    m=dec(s.Matrix(s.symbols('m0:15'))); f,j=s.symbols('f j'); z=m[n,n]
    zeta=s.Matrix([*s.symbols('z0:4'),0]); nn=s.eye(D)[:,n]; nn=nn*nn.T
    jump=2*j*m+j*z*eta+9*j*z*nn-6*j*ins(n,zeta)*f
    exponents=op(lambda p:s.Matrix(D,D,lambda a,b:(2+3*int(int(a)==n)+3*int(int(b)==n))*p[a,b]))
    jump_u=dec(enc(jump)+j*(R/2-exponents)*enc(m))
    assert all(s.expand(jump_u[a,b]-j*z*eta[a,b]-3*j*m[a,b]/2)==0 for a in range(4) for b in range(4))
    assert all(s.expand(jump_u[a,n]+5*j*m[a,n]/2+6*j*zeta[a]*f)==0 for a in range(4))
    assert s.expand(jump_u[n,n]-3*j*z/2-j*s.trace(eta[:4,:4]*m[:4,:4]))==0
    d=-f*(2*j*eta+6*j*nn)
    correction=dec((exponents-R/2)*enc(d))[n,n]*j/4
    assert s.expand(4+11*j*j+correction/f/2)==4+3*j*j/2
    # At frozen tangential point, ell^2=s_time^2+|xi|², alpha=Re ell.
    # |zeta|<=sqrt(2)*alpha*|ell|/gamma, verified by polynomial identity.
    A,B,g=s.symbols('alpha beta gamma',real=True)
    assert s.expand(2*A*A*(A*A+B*B)-(g*g*(A*A-B*B)+2*A*A*B*B))==A*A*(2*A*A-g*g)+g*g*B*B or s.expand(2*A*A*(A*A+B*B)-(g*g*(A*A-B*B)+2*A*A*B*B)-(A*A*(2*A*A-g*g)+g*g*B*B))==0
    # For gamma sufficiently large, matrix Green contraction and endpoint
    # derivative error <= epsilon*|ell|*max endpoint amplitude.
    # use sqrt(2)<2. rho<=6*(2c1/gamma+c0/gamma²).
    gam=s.Integer(10**7); rho=6*(2*c1/gam+c0/gam**2)
    err=18*(2*c1/gam+c0/gam**2)/(1-rho)
    assert rho<s.Rational(1,100) and err<s.Rational(1,100)
    # Reference forced 16-channel relation: scaled X=max(|ell| |m|, |ell|² |f|).
    # diagonal: -2ell tanh for m; ell² for f. off diagonal tilt <=6|j|/gamma.
    # d=-Jf+a, |J|_infty=8|j|. At zero forcing max endpoints <= (1+4|j|/gamma) X/|ell|.
    # Each DtoN derivative error <= err*(1+4|j|/gamma)*X.
    # Wall row includes half mean derivative and flat d term, <= |j|*8/(4gamma), plus constant.
    jabs=s.Rational(6,5)
    off_m= (s.Rational(11,2)*jabs+6*jabs)/gam+2*err*(1+4*jabs/gam)
    off_f=2*jabs*s.Rational(4,3)/gam+(4+s.Rational(3,2)*jabs**2)/gam**2+err*(1+4*jabs/gam)/2
    assert off_m<s.Rational(1,2) and off_f<s.Rational(1,2)
    # Independent exact coordinate jet controls at midpoint and one wall side.
    p0=dec(s.Matrix([s.Rational(i-7,5) for i in range(15)])); p1=dec(s.Matrix([s.Rational((i*i)%13-6,7) for i in range(15)])); p2=dec(s.Matrix([s.Rational((i*3)%11-5,3) for i in range(15)])); zz=[2,-3,5,1]
    for b0,k0 in [(s.Rational(4,5),s.S.Zero),(s.S.One,s.Rational(3,5))]:
        expect=enc(p2)+b0*k0*R*enc(p1)+sum(eta[a,a]*zz[a]**2 for a in range(4))*enc(p0)+b0*k0*sum((J[a]*zz[a] for a in range(4)),s.zeros(15))*enc(p0)+(b0*b0*(Vwarp+Vcurv)+h2*(-Vwarp+Vnormal-Vbase))*enc(p0)
        direct_jet(b0,k0,p0,p1,p2,zz,expect)
    print('PASS two independent full coordinate Ricci/gauge jet controls')
    print('PASS full 15-component frame, RNC jets, diagonalization, moving seam and damped 16-channel bound')
    print('R projectors ranks:',[Q.rank() for Q in projectors],'condition bound',cond,'c1,c0',c1,c0)
    print('gamma',gam,'rho',float(rho),'relative endpoint error',float(err),'row bounds',float(off_m),float(off_f))

# Independent jet linearization of coordinate Ricci and lower contracted Gamma.
def direct_jet(b0,k0,p0,p1,p2,zeta,expected):
    from itertools import product
    ix=range(5); h2=s.Rational(16,25); K=-h2
    z=s.Matrix(s.symbols('q0:5')); y=z[4]; Z=z[:4,0]; E=eta[:4,:4]; ZZ=E*Z; q=(Z.T*E*Z)[0]
    h=E-K*(q*E-ZZ*ZZ.T)/3
    b=b0+b0**5*k0*y+b0**9*(1+4*k0*k0)*y*y/2
    X=b0**3*y+3*b0**7*k0*y*y/2
    # Second-order Taylor polynomials in total degree, truncate before differentiating.
    def trunc(a):return s.Add(*(c*s.prod(z[i]**m[i] for i in ix) for m,c in s.Poly(a,*z).terms() if sum(m)<=2))
    g=s.diag(1,1,1,1,1); g[:4,:4]=b*b*h;g[4,4]=b**8
    phase=sum(zeta[a]*z[a] for a in range(4)); pbar=(p0+p1*X+p2*X*X/2)*(1+phase+phase**2/2)
    p=s.Matrix(5,5,lambda i,j:trunc(b**(2+3*int(int(i)==4)+3*int(int(j)==4))*pbar[i,j]))
    g=g.applyfunc(trunc); zero=dict.fromkeys(z,0)
    g0=g.subs(zero); p=p.applyfunc(s.expand); p00=p.subs(zero); inv=g0.inv(); di=-inv*p00*inv
    dg=[g.diff(a).subs(zero) for a in z]; dp=[p.diff(a).subs(zero) for a in z]
    ddg=[[g.diff(a,c).subs(zero) for c in z] for a in z]; ddp=[[p.diff(a,c).subs(zero) for c in z] for a in z]
    invd=[-inv*dg[a]*inv for a in ix]; did=[-invd[a]*p00*inv-inv*dp[a]*inv-inv*p00*invd[a] for a in ix]
    H=lambda a,i,j: (dg[i][a,j]+dg[j][a,i]-dg[a][i,j])/2
    Hp=lambda a,i,j: (dp[i][a,j]+dp[j][a,i]-dp[a][i,j])/2
    Hd=lambda k,a,i,j:(ddg[k][i][a,j]+ddg[k][j][a,i]-ddg[k][a][i,j])/2
    Hpd=lambda k,a,i,j:(ddp[k][i][a,j]+ddp[k][j][a,i]-ddp[k][a][i,j])/2
    G={}; DG={}; Gd={}; DGd={}
    for a,i,j in product(ix,repeat=3):
        G[a,i,j]=sum(inv[a,l]*H(l,i,j) for l in ix)
        DG[a,i,j]=sum(di[a,l]*H(l,i,j)+inv[a,l]*Hp(l,i,j) for l in ix)
        for k in ix:
            Gd[k,a,i,j]=sum(invd[k][a,l]*H(l,i,j)+inv[a,l]*Hd(k,l,i,j) for l in ix)
            DGd[k,a,i,j]=sum(did[k][a,l]*H(l,i,j)+di[a,l]*Hd(k,l,i,j)+invd[k][a,l]*Hp(l,i,j)+inv[a,l]*Hpd(k,l,i,j) for l in ix)
    C=s.Matrix([sum(inv[i,j]*G[a,i,j] for i,j in product(ix,repeat=2)) for a in ix]); DC=s.Matrix([sum(di[i,j]*G[a,i,j]+inv[i,j]*DG[a,i,j] for i,j in product(ix,repeat=2)) for a in ix])
    assert C==s.zeros(5,1)
    DClo=p00*C+g0*DC
    DdC=[]
    for k in ix:
        Cd=s.Matrix([sum(invd[k][i,j]*G[a,i,j]+inv[i,j]*Gd[k,a,i,j] for i,j in product(ix,repeat=2)) for a in ix])
        DCd=s.Matrix([sum(did[k][i,j]*G[a,i,j]+di[i,j]*Gd[k,a,i,j]+invd[k][i,j]*DG[a,i,j]+inv[i,j]*DGd[k,a,i,j] for i,j in product(ix,repeat=2)) for a in ix])
        DdC.append(dp[k]*C+p00*Cd+dg[k]*DC+g0*DCd)
    out=s.zeros(5)
    for i,j in ids:
        dRic=sum(DGd[a,a,i,j]-DGd[j,a,i,a] for a in ix)+sum(DG[a,a,l]*G[l,i,j]+G[a,a,l]*DG[l,i,j]-DG[a,j,l]*G[l,i,a]-G[a,j,l]*DG[l,i,a] for a,l in product(ix,repeat=2))
        dGauge=(DdC[i][j]+DdC[j][i])/2-sum(G[a,i,j]*DClo[a] for a in ix)
        out[i,j]=out[j,i]=-2*b0*b0*(dRic+4*p00[i,j]-dGauge)/b0**(2+3*int(i==4)+3*int(j==4))
    assert enc(out)==expected,(enc(out)-expected)

if __name__=='__main__':derive()
