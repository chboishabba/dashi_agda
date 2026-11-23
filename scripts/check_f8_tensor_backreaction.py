"""F8 full angular reconstruction and quadratic Ricci diagnostic.
Original #1527 Q=diag(0,1,-1), d=3,7,11; #1530 quadratic source.
No full discrete TT, nonlinear evolution or continuum claim.
"""
import sympy as s
import numpy as np
from math import asinh,sqrt,ceil,log
from check_f8_ym_ns_weld import source
from scipy.optimize import brentq


def angular():
    x,y,w,R=s.symbols('x y w R',real=True); xyz=(x,y,w); r2=x*x+y*y+w*w
    j=s.symbols('j0:9'); H=s.symbols('H0:3'); lams=(0,2,4)
    def der(f,i):return s.diff(f,xyz[i])+2*xyz[i]*sum(s.diff(f,j[k])*j[k+1] for k in range(8))
    def P(i,k,f):return s.expand((sum(der(der(f,a),a) for a in range(3)) if i==k else 0)-der(der(f,i),k))
    A=s.Matrix(3,3,lambda i,k:P(i,1,P(k,1,j[0]))-P(i,2,P(k,2,j[0]))-P(i,k,P(1,1,j[0])-P(2,2,j[0]))/2)
    f1=2*R*j[1];f2=2*j[1]+4*R**2*j[2];f3=12*R*j[2]+8*R**3*j[3];f4=12*j[2]+48*R**2*j[3]+16*R**4*j[4]
    profile=s.Matrix([s.Rational(2,5)*(f4+4*f3/R),s.Rational(4,7)*(f4+f3/R-6*f2/R**2+6*f1/R**3), (f4-6*f3/R+15*f2/R**2-15*f1/R**3)/35])
    M=profile.jacobian(j[2:5]); assert s.factor(M.det())!=0
    repl=dict(zip(j[2:5],M.inv()*s.Matrix([H[i]*R**lams[i] for i in range(3)])))
    B=s.zeros(3);polys=[]
    for i,l in enumerate(lams):
        P0=A.subs(repl,simultaneous=True).diff(H[i]); P0=P0.applyfunc(lambda a:s.cancel(a.subs(R**2,r2)))
        P0=P0.applyfunc(s.cancel)
        # Lifting H_l/r^l to a Cartesian homogeneous harmonic tensor.
        assert all(s.denom(a)==1 or s.denom(a).is_number for a in P0)
        assert all(s.expand(sum(s.diff(a,q,2) for q in xyz))==0 for a in P0)
        assert all(s.expand(sum(q*s.diff(a,q) for q in xyz)-l*a)==0 for a in P0)
        assert s.expand(s.trace(P0))==0
        assert s.simplify(P0[1,1].subs({y:0,w:0})-x**l)==0
        polys.append(P0)
    # Actual prepotential compatibility in u=r^2, unscaled regularized profiles.
    uu=s.symbols('uu'); U=[s.cancel(profile[i]/R**lams[i]).subs(R**2,uu) for i in range(3)]
    UD=lambda f:s.diff(f,uu)+sum(s.diff(f,j[k])*j[k+1] for k in range(8))
    assert s.expand(UD(U[1])-90*U[2]-20*uu*UD(U[2]))==0
    assert s.expand(UD(U[0])-s.Rational(7,4)*U[1]-63*uu*U[2]-14*uu**2*UD(U[2]))==0
    # Arbitrary radial jet inversion/reconstruction, and exact divergence defect.
    recon=sum((polys[i]*profile[i]/R**lams[i] for i in range(3)),s.zeros(3))
    assert all(s.cancel(s.cancel(a-b).subs(R**2,r2))==0 for a,b in zip(recon,A))
    assert all(s.expand(sum(der(A[i,k],i) for i in range(3)))==0 for k in range(3))
    print('PASS: 3 full tensor harmonic lifts; trace, harmonic degree, receiver normalization, arbitrary radial jet reconstruction, TT divergence',flush=True)
    return xyz,polys


def radial(d,n,dr):
    j=np.arange(n,dtype=float);W=((j+.5)**d-np.maximum(j-.5,0)**d)/d;F=(j+.5)**(d-1)/dr**2
    return -(F+np.r_[0.,F[:-1]])/W,F[:-1]/W[:-1],F[:-1]/W[1:]


def evolve(dr=.012,dy=.03,dt=.003,eps=.04,final=12.,pulse=.065):
    # Reconstructed original normal_order=3 stage, zero outer radial node eliminated.
    F=lambda t:asinh(t)-sqrt(1+t*t)/t
    T0=F(1);span=F(final)-T0;nt=ceil(span/dt);dt=span/nt
    n=ceil(3.2/dr);ny=ceil(2.1/dy)+1;r=np.arange(n)*dr;Y=np.arange(ny)*dy
    src=source(r,dr,eps);rx=sqrt(span**2-(1-1/final)**2)-.012
    assert rx-eps-log(final)>dr/2 and dr<eps/3
    # Capture a local five-time by five-normal by five-radial stencil, including off-axis data.
    ir=int(rx/dr);iy=2;it=nt-3;rs=slice(ir-2,ir+3);ys=slice(iy-2,iy+3)
    assert ir+2<n
    geom=[]
    for k in range(2*(nt+1)+1):
        ds=k*dt/2;t=brentq(lambda t:F(t)-T0-ds,.5,final+2);v=-1/sqrt(1+t*t);b=1/t
        amp=-6*sqrt(1-v*v)/b*np.exp(1-1/(1-(2*ds/pulse-1)**2)) if 0<ds<pulse else 0.
        geom.append((1+v,1-v,1.5/(b+Y)[:,None],amp))
    def D(x):
        z=np.empty_like(x);z[0]=(x[1]-x[0])/dy;z[-1]=(x[-1]-x[-2])/dy;z[1:-1]=(x[2:]-x[:-2])/(2*dy);return z
    hist=[]
    for q,d in enumerate((3,7,11)):
        diag,plus,minus=radial(d,n,dr);state=np.zeros((3,ny,n));snap=[]
        def B(state,k):
            U,P,M=state;a,c,Z,amp=geom[k];force=U*diag;force[:,:-1]+=plus*U[:,1:];force[:,1:]+=minus*U[:,:-1];force-=Z*(P-M)
            p=a*D(P)+force;m=-c*D(M)+force;p[-1]-=2*a*P[-1]/dy;m[0]+=2*(a*P[0]-c*M[0]-2*amp*src[q])/dy
            return state+dt*np.array([(a*P+c*M)/2,p,m])
        for k in range(nt+2):
            if abs(k-it)<=2:snap.append(state[0,ys,rs].copy())
            if k==nt+1:break
            a=B(state,2*k);b=.75*state+.25*B(a,2*k+2);state=state/3+2*B(b,2*k+1)/3
        hist.append(snap)
    T=T0+it*dt;t=brentq(lambda t:F(t)-T,.5,final+2);b=1/t;v=-1/sqrt(1+t*t);acc=t**3/(1+t*t)**2
    print('evolved grid',n,ny,nt,'sample r,Y,t',r[ir],Y[iy],t,flush=True)
    return np.array(hist), (dt,dy,dr,eps,r[ir],b+Y[iy],v,acc)


def weights(h):
    a=np.arange(-2,3,dtype=float)*h
    return np.linalg.solve(np.array([a**k for k in range(5)]), np.diag([1.,1.,2.,6.,24.])).T[:3]


def field_jets(xyz,polys,hist,params):
    dt,dy,dr,eps,r,z,v,acc=params
    # Off-axis point, retain every angular component.
    n=np.array([2.,3.,6.])/7;point=n*r
    W=[weights(h) for h in (dt,dy,dr)]
    # Derivatives of each regularized V_l in (T,Y,r), then transform Y=z-b(T).
    H=np.zeros((5,5));dH=np.zeros((5,5,5));ddH=np.zeros((5,5,5,5))
    dirs=np.zeros((5,3));dirs[0]=[1,-v,0];dirs[4]=[0,1,0];dirs[1:4,2]=n
    ddcoords=np.zeros((5,5,3));ddcoords[0,0,1]=-acc;ddcoords[1:4,1:4,2]=(np.eye(3)-np.outer(n,n))/r
    for q,l in enumerate((0,2,4)):
        D=lambda i,j,k:np.einsum('a,b,c,abc->',W[0][i],W[1][j],W[2][k],hist[q])
        f=D(0,0,0); grad=np.array([D(1,0,0),D(0,1,0),D(0,0,1)]);hes=np.array([[D(2,0,0),D(1,1,0),D(1,0,1)],[D(1,1,0),D(0,2,0),D(0,1,1)],[D(1,0,1),D(0,1,1),D(0,0,2)]])
        df=dirs@grad;ddf=dirs@hes@dirs.T+ddcoords@grad
        A=polys[q]/eps**l
        ev=lambda a:np.array(a.subs(dict(zip(xyz,point))),dtype=float)
        p=ev(A);dp=np.zeros((5,3,3));ddp=np.zeros((5,5,3,3))
        for i,x in enumerate(xyz,1):
            dp[i]=ev(A.diff(x))
            for j,y in enumerate(xyz,1):ddp[i,j]=ev(A.diff(x,y))
        H[1:4,1:4]+=p*f
        for a in range(5):
            dH[a,1:4,1:4]+=dp[a]*f+p*df[a]
            for b in range(5):ddH[a,b,1:4,1:4]+=ddp[a,b]*f+dp[a]*df[b]+dp[b]*df[a]+p*ddf[a,b]
    # Convert dimensionless conformal perturbation into covariant metric jets.
    sc=1/z**2;ds=np.zeros(5);ds[4]=-2/z**3;dds=np.zeros((5,5));dds[4,4]=6/z**4
    u=r*r
    V=np.array([np.einsum('a,b,c,abc->',W[0][0],W[1][0],W[2][0],hist[q])/eps**(2*q) for q in range(3)])
    Vp=np.array([np.einsum('a,b,c,abc->',W[0][0],W[1][0],W[2][1],hist[q])/eps**(2*q)/(2*r) for q in range(3)])
    print('prepotential compatibility residuals',Vp[1]-90*V[2]-20*u*Vp[2],Vp[0]-7*V[1]/4-63*u*V[2]-14*u*u*Vp[2])
    return H*sc,dH*sc+ds[:,None,None]*H,ddH*sc+ds[:,None,None,None]*dH[None]+ds[None,:,None,None]*dH[:,None]+dds[:,:,None,None]*H


def ricci_jet(h,dh,ddh,z):
    eta=np.diag([-1.,1,1,1,1]);g=eta/z**2;inv=eta*z*z;B=np.zeros((5,5,5))
    for m,a,b in np.ndindex(5,5,5):B[m,a,b]=(-(a==m)*(b==4)-(a==b)*(m==4)+eta[m,b]*eta[a,4])/z
    dB=np.zeros((5,5,5,5));dB[4]=-B/z;dinv=np.zeros((5,5,5));dinv[4]=2*z*eta
    C=np.empty_like(B);dC=np.empty_like(dB)
    cov=np.array([dh[m]-B[m].T@h-h@B[m] for m in range(5)])
    dcov=np.array([[ddh[k,m]-dB[k,m].T@h-B[m].T@dh[k]-dh[k]@B[m]-h@dB[k,m] for m in range(5)] for k in range(5)])
    for m in range(5):
        A=np.array([[cov[m,c,b]+cov[b,c,m]-cov[c,m,b] for b in range(5)] for c in range(5)])/2;C[m]=inv@A
        for k in range(5):
            dA=np.array([[dcov[k,m,c,b]+dcov[k,b,c,m]-dcov[k,c,m,b] for b in range(5)] for c in range(5)])/2
            dC[k,m]=dinv[k]@A+inv@dA
    D=np.array([-inv@h@C[m] for m in range(5)]);dD=np.array([[-dinv[k]@h@C[m]-inv@dh[k]@C[m]-inv@h@dC[k,m] for m in range(5)] for k in range(5)])
    def Ric(A,dA):
        covar=lambda m,n:dA[m,n]+B[m]@A[n]-A[n]@B[m]-sum(B[m,k,n]*A[k] for k in range(5))
        return np.array([[sum((covar(a,n)-covar(n,a))[a,b] for a in range(5)) for n in range(5)] for b in range(5)])
    Q=Ric(D,dD)+np.array([[sum((C[a]@C[n]-C[n]@C[a])[a,b] for a in range(5)) for n in range(5)] for b in range(5)])
    div=np.array([sum(inv[a,k]*cov[a,k,n] for a in range(5) for k in range(5)) for n in range(5)])
    return Q,Ric(C,dC)+4*h,div


def validate_jet():
    # Independently compare numerical jet implementation to the committed symbolic
    # quadratic operator, on the previous exact polarized null wave.
    from pathlib import Path
    ns={};code=Path(__file__).with_name('check_f8_quadratic_einstein.py').read_text().split('# Three nontrivial TT waves')[0]
    exec(code,ns);X=ns['X'];T,x,y,w,z=X;H=s.diag(0,0,2*(T-x)**2,-2*(T-x)**2,0)/z**2
    point=dict(zip(X,[s.Rational(2,3),s.Rational(1,5),0,0,s.Rational(3,4)]))
    ev=lambda A:np.array(A.subs(point),dtype=float)
    Q,lin,div=ricci_jet(ev(H),np.array([ev(H.diff(a)) for a in X]),np.array([[ev(H.diff(a,b)) for b in X] for a in X]),.75)
    assert np.allclose(Q,ev(ns['quadratic'](H)),rtol=1e-12,atol=1e-12)
    assert np.linalg.norm(lin)<1e-12 and np.linalg.norm(div)<1e-12
    print('PASS: pointwise Ricci jet evaluator vs committed symbolic quadratic operator')


def junction():
    # Fixed original embedding and block-spatial metric only: mixed K = Kbar I + 1/2 M^-1 n(M).
    e=s.symbols('e');H=s.Matrix([[1,2,0],[2,-1,1],[0,1,0]]);N=s.Matrix([[2,0,1],[0,1,0],[1,0,-3]]);K=s.diag(3,4,5);J=s.diag(2,3,4)
    M=s.eye(3)+e*H+e**2*K;inv=s.eye(3)-e*H+e**2*(H*H-K)
    assert (inv*M).applyfunc(lambda a:s.expand(a).series(e,0,3).removeO())==s.eye(3)
    A=(inv*(e*N+e**2*J)/2).applyfunc(lambda a:s.expand(a).coeff(e,2))
    assert A==(J-H*N)/2
    assert s.trace(A)==(s.trace(J)-s.trace(H*N))/2
    print('PASS: fixed-embedding spatial mixed Israel curvature second-order term (nK-H nH)/2; full lapse/shift/embedding/junction open')

if __name__=='__main__':
    xyz,polys=angular();junction();validate_jet();hist,p=evolve();h,dh,ddh=field_jets(xyz,polys,hist,p);Q,lin,div=ricci_jet(h,dh,ddh,p[5]);assert np.isfinite(Q).all();assert np.allclose(Q,Q.T,rtol=1e-8,atol=1e-12)
    print('off-axis evolved metric h norm',np.linalg.norm(h),'Q norm',np.linalg.norm(Q),'linear residual norm',np.linalg.norm(lin),'TT divergence norm',np.linalg.norm(div),'quadratic symmetry residual',np.linalg.norm(Q-Q.T));print(Q)
