"""F8 spatial mean scalar closure by planar mass; finite band diagnostic only."""
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp
from scipy.interpolate import CubicSpline
from scipy.special import roots_legendre
from check_f8_tt_retarded import galerkin, geometry
from check_f8_original_zero_history import radial_coefficient, bump, history


def exact():
    r,X,p=s.symbols('r X p'); d=s.Matrix(s.symbols('d:2')); g=s.diag(-1,1)
    F=s.Matrix([[s.Symbol('F00'),s.Symbol('F01')],[s.Symbol('F01'),s.Symbol('F11')]])
    H=-r*(F-g*s.trace(g*F)/2)/3+g*(4*r-2*X/r-r*p)/2
    target=r**3*(p*d+s.Rational(2,3)*(F-g*s.trace(g*F)/2)*g*d)
    assert ((4*r**3-2*r*X)*d-2*r*r*H*g*d-target).applyfunc(s.expand)==s.zeros(2,1)
    T,r=s.symbols('T r',real=True,positive=True); U=s.Function('U')(T,r)
    Wtt,Wrr,Wtr,Wxx=s.symbols('Wtt Wrr Wtr Wxx')
    Qtt=-U.diff(T,2)/(2*r*r)+r*U.diff(r)/2+Wtt/(2*r*r)
    Qrr=r*r*U.diff(r,2)/2+3*r*U.diff(r)/2-r*r*Wrr/2
    QTr=r*r*(U.diff(T,r)-Wtr)/2
    Qp=(-U.diff(T,2)/r**2+r*r*U.diff(r,2)+2*r*U.diff(r))/6+r*U.diff(r)-Wxx/(6*r*r)
    Mr=-r**3*(Qp+(Qrr-Qtt)/3); MT=-2*r**3*QTr/3; shift=r**5*U.diff(r)/3
    assert s.expand(Mr+shift.diff(r)-(r**5*Wrr+r*(Wtt+Wxx))/6)==0
    assert s.expand(MT+shift.diff(T)-r**5*Wtr/3)==0
    da=-r*U/6
    assert s.expand(2*r**3*da-2*r**4*da.diff(r)-shift)==0
    x=s.symbols('x',real=True); f=s.Function('f')(T,r,x)
    dens=(r**5*f.diff(r)**2+r*(f.diff(T)**2+f.diff(x)**2))/6; flux=r**5*f.diff(r)*f.diff(T)/3
    wave=r*f.diff(T,2)-(r**5*f.diff(r)).diff(r)-r*f.diff(x,2)
    assert s.expand(dens.diff(T)-flux.diff(r)-r*(f.diff(T)*f.diff(x)).diff(x)/3-f.diff(T)*wave/3)==0
    t=s.symbols('t',positive=True); b=1/t; K=s.Function('K')(t); w=s.Function('w')(t)
    y,u,d=s.Function('y')(t),s.Function('u')(t),s.Function('d')(t); hh=s.symbols('hh')
    dr=-3*w*y+K*u.diff(t)-3*b*K*u-d; dp=-w*y+K*u.diff(t)+(K.diff(t)+3*b*K)*u+d/3
    conservation=dr.diff(t)+3*b*(dr+dp)+3*(K+w)*y.diff(t)+hh
    clock=K*(u.diff(t,2)+(3*b+K.diff(t)/K)*u.diff(t)+3*b*b*u+3*y.diff(t))
    assert s.expand((conservation-clock+d.diff(t)+2*b*d-hh).subs(w.diff(t),-4*b*w))==0
    e=s.symbols('e'); beta=s.sqrt(1+b*b); mass,dr0=s.symbols('mass dr0'); radius=t*(1+e*y)
    residual=(radius.diff(t)/radius)**2-(beta+e*dr0)**2+1-e*mass/radius**4
    assert s.simplify(residual.diff(e).subs(e,0)-(2*b*y.diff(t)-2*beta*dr0-mass/t**4))==0
    c,v0,vn,vx=s.symbols('c v0 vn vx',real=True)
    assert s.expand(c*(v0*v0+vn*vn+vx*vx)+2*v0*vn-((v0+vn)**2+(c-1)*(v0*v0+vn*vn)+c*vx*vx))==0
    print('8 exact mass, current, volume and wall-constraint checks PASS',flush=True)


def areal_exact():
    # Independent coordinate-linearized Ricci of areal metric, arbitrary M and lapse.
    T,r=s.symbols('T r',real=True,positive=True); X=(T,r); ix=range(2)
    M=s.Function('M')(T,r); d=s.Function('d')(T,r); g=s.diag(-r*r,r**-2); gi=g.inv()
    h=s.diag(M/r**2-2*r*r*d,M/r**6); di=-gi*h*gi
    from itertools import product
    G={}; C={}
    for a,i,j in product(ix,repeat=3):
        G[a,i,j]=sum(gi[a,k]*(g[k,j].diff(X[i])+g[k,i].diff(X[j])-g[i,j].diff(X[k]))/2 for k in ix)
        C[a,i,j]=sum((di[a,k]*(g[k,j].diff(X[i])+g[k,i].diff(X[j])-g[i,j].diff(X[k]))+gi[a,k]*(h[k,j].diff(X[i])+h[k,i].diff(X[j])-h[i,j].diff(X[k])))/2 for k in ix)
    R=s.Matrix(2,2,lambda i,j:sum(C[k,i,j].diff(X[k])-C[k,i,k].diff(X[j]) for k in ix)+sum(G[k,k,l]*C[l,i,j]+C[k,k,l]*G[l,i,j]-G[k,j,l]*C[l,i,k]-C[k,j,l]*G[l,i,k] for k,l in product(ix,repeat=2)))
    F=gi*(R+3*s.Matrix(2,2,lambda i,j:C[1,i,j])/r+4*h)
    # Mixed defect background zero, so raising with background is exact at this order.
    ep=-(r*sum(-di[i,j]*G[1,i,j]-gi[i,j]*C[1,i,j] for i,j in product(ix,repeat=2))+2*di[1,1])/r**2
    assert s.simplify(F[1,1]-F[0,0]-3*r*d.diff(r))==0
    assert s.simplify(r**3*(ep+(F[1,1]-F[0,0])/3)-M.diff(r))==0
    assert s.simplify(2*r**3*F[1,0]/3-M.diff(T))==0
    # Source Bianchi: mass-current curl equals minus temporal trace-reversed divergence.
    a,b,p,j=[s.Function(name)(T,r) for name in ('a','b','p','j')]
    divT=(a-b-3*p).diff(T)/2+j.diff(r)+3*j/r
    assert s.expand((r**3*(p+(b-a)/3)).diff(T)-(2*r**3*j/3).diff(r)+2*r**3*divT/3)==0
    # The mean-volume shift changes the Ricci source to positive first-derivative products.
    U=s.Function('U')(T,r); v=-U/6
    H=s.Matrix(2,2,lambda i,j:U.diff(X[i],X[j])-sum(G[k,i,j]*U.diff(X[k]) for k in ix))
    D=s.Matrix([0,1/r]); DU=s.Matrix([U.diff(q) for q in X]); W=s.Matrix(2,2,s.symbols('W:4'))
    Q=H/2+(D*DU.T+DU*D.T)/2-W/2
    HV=s.Matrix(2,2,lambda i,j:v.diff(X[i],X[j])-sum(G[k,i,j]*v.diff(X[k]) for k in ix)); DV=s.Matrix([v.diff(q) for q in X])
    assert (-Q-3*(HV+D*DV.T+DV*D.T)-W/2).applyfunc(s.simplify)==s.zeros(2)
    assert s.simplify(-(-U.diff(T,2)/r**2+r*r*U.diff(r,2)+2*r*U.diff(r))/6-r*U.diff(r)-s.trace(gi*HV)-6*(D.T*gi*DV)[0])==0
    print('6 independent areal Ricci, Bianchi and effective source checks PASS',flush=True)


def areal_reconstruct(T,r,source,outer=.25):
    """Integrate fixed-T homogeneous mean metric. Source supplies W_TT,W_rr,W_xx.
    Returns mass and lapse corrections with zero exterior anchor; caller provides
    compatible history across the entire fixed-T slice (not just a wall sample).
    """
    from scipy.integrate import quad
    def mr(a):
        wt,wr,wx=source(T,a); return (a**5*wr+a*(wt+wx))/6
    def dr(a):
        wt,wr,_=source(T,a); return (a*wr+wt/a**3)/6
    return quad(mr,outer,r)[0],quad(dr,outer,r)[0]


def bump_derivative(t):
    T=np.arcsinh(t)-np.sqrt(1+t*t)/t-(np.arcsinh(1.)-np.sqrt(2.)); x=2*T/.065-1
    if abs(x)>=1:return 0.
    return bump(t)*(-2*x/(1-x*x)**2)*(2/.065)*np.sqrt(1+t*t)/t**2


def bump_second(t):
    T=np.arcsinh(t)-np.sqrt(1+t*t)/t-(np.arcsinh(1.)-np.sqrt(2.)); x=2*T/.065-1
    if abs(x)>=1:return 0.
    xp=2/.065*np.sqrt(1+t*t)/t**2; xpp=xp*(t/(1+t*t)-2/t)
    lp=-2*x/(1-x*x)**2; lpp=-2/(1-x*x)**2-8*x*x/(1-x*x)**3
    return bump(t)*((lp*lp+lpp)*xp*xp+lp*xpp)


def profile(n):
    d=.3; r=np.asarray(n)/d; b=np.maximum(0.,1-r)
    return n*b**6, b**6-6*r*b**5, (-12*b**5+30*r*b**4)/d


def lifted_history(k,ci,final,modes,quad):
    def g(t):return -6*ci*bump(t)
    def gt(t):return -6*ci*bump_derivative(t)
    def gtt(t):return -6*ci*bump_second(t)
    def F(t,n):
        a,N=geometry(t,n); c=np.sqrt(1+a*a); bt=np.sqrt(1+t*t)
        Nt=N*(a/c-t/bt)/bt; Nn=-a/bt
        p,dp,ddp=profile(n)
        return -((-gtt(t)/N**2+(Nt/N**3-3/(a*N))*gt(t))*p+g(t)*(ddp+(Nn/N-3*c/a)*dp-k*k*p/a**2))
    sol=galerkin(k,F,lambda t:0.,1.,final,modes,quad)[1]
    def evaluate(t,n):
        h,ht,hn=history(sol,t,n,modes,quad); p,dp,_=profile(n)
        return h+g(t)*p,ht+gt(t)*p,hn+g(t)*dp
    return evaluate


def run(cutoff=80.,nodes=8,modes=12,final=1.2,quad=80,lift=True):
    q,w=roots_legendre(nodes); k=cutoff*(q+1)/2; w=cutoff*w/2
    coeff=np.array([radial_coefficient(v,1.) for v in k])
    sols=[lifted_history(v,c,final,modes,quad) for v,c in zip(k,coeff)] if lift else [galerkin(v,lambda t,n:np.zeros_like(n),lambda t,c=c:-6*c*bump(t),1.,final,modes,quad)[1] for v,c in zip(k,coeff)]
    evaluate=lambda sol,t,n:sol(t,n) if lift else history(sol,t,n,modes,quad)
    r,wn=roots_legendre(quad); r=(r+1)/2; wn=wn/2
    times=np.linspace(1.,final,241); masses=[]; ds=[]; drive=[]; flux=[]
    for t in times:
        L=np.arcsinh(t)-np.arcsinh(.25); n=L*r; a,N=geometry(t,n); c=np.sqrt(1+a*a)
        integ=np.zeros_like(n); cross=0.; wallflux=0.
        for ki,wi,ci,sol in zip(k,w,coeff,sols):
            h,ht,hn=evaluate(sol,t,n); ht=ht/N; weight=wi*ki**2/(5*np.pi**2)
            integ+=weight*a**3/6*(c*(ht**2+hn**2+ki**2*h**2/a**2)+2*ht*hn)
            h0,ht0,_=evaluate(sol,t,0.); hn0=-6*ci*bump(t)
            cross+=weight*ci*h0
            wallflux+=weight*t**3/6*(-ht0**2-hn0**2+ki**2*h0**2/t**2-2*np.sqrt(1+t*t)*ht0*hn0)
        mass=L*np.dot(wn,integ); assert mass>=-1e-20
        masses.append(mass);ds.append(bump(t)*cross);drive.append((2*bump(t)/t+bump_derivative(t))*cross);flux.append(wallflux)
    M,D,F=map(lambda v:CubicSpline(times,v), (masses,ds,drive))
    def rhs(t,z):
        y,u,v=z; b=1/t; B=np.sqrt(1+b*b); w=b**4/12; K=b*b/(3*B)-w
        Kt=-b**3*(2+b*b)/(3*B**3)+4*b*w
        dr=-3*w*y+K*v-3*b*K*u-D(t); yt=t*B*dr+M(t)/(2*t**3)
        return [yt,v,-(3*b+Kt/K)*v-3*b*b*u-3*yt+F(t)/K]
    sol=solve_ivp(rhs,(1.,final),[0.,0.,0.],rtol=1e-9,atol=1e-13,dense_output=True)
    assert sol.success and np.all(np.isfinite(sol.y)) and max(masses)>0
    flux_error=np.max(abs(M(times,1)-flux))/max(1e-30,np.max(np.abs(flux)))
    print('lift,cutoff,nodes,modes',lift,cutoff,nodes,modes,'mass final',masses[-1],'area/clock/velocity',sol.y[:,-1].tolist(),'relative sampled mass flux defect',flux_error,flush=True)
    return masses[-1],sol.y[:,-1],flux_error

if __name__=='__main__':
    exact(); areal_exact()
    for m in (12,24,48):run(modes=m)
