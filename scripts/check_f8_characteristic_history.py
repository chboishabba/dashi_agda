"""Independent original short-time radial histories using characteristic upwind.
Actual GN geometry; causal outer n=.5 for t<=1.2. Numerical diagnostic only.
"""
import numpy as np
from scipy.special import roots_legendre
from scipy.integrate import cumulative_trapezoid, simpson


def coefficient(k):
    x,w=roots_legendre(192);u=(x+1)/2;f=np.exp(1-1/(1-u*u));k=np.asarray(k)
    return 4*np.pi*.04**7*k**4*(np.sinc(k[:,None]*.04*u/np.pi)@(w*u*u*f/2))


def bump(t):
    d=np.arcsinh(t)-np.sqrt(1+t*t)/t-(np.arcsinh(1.)-np.sqrt(2.))
    x=2*d/.065-1
    return np.exp(1-1/(1-x*x)) if abs(x)<1 else 0.


def evolve(k,ci,cells=512,final=1.2,sample_n=None):
    if not 1<final<=1.2:raise ValueError('short causal slab only')
    n=np.linspace(0,.5,cells+1);dn=n[1];steps=int(np.ceil((final-1)/(.3*dn)));dt=(final-1)/steps
    k=np.asarray(k)[:,None];ci=np.asarray(ci); y=np.zeros((3,len(k),len(n)))
    def geo(t):
        q=np.arcsinh(t)-n;a=np.sinh(q);c=np.cosh(q);N=c/np.sqrt(1+t*t)
        return a,c,N,-a/np.sqrt(1+t*t)
    def enforce(t,y):
        y[2,:,0]=y[1,:,0]+12*ci*bump(t);y[1,:,-1]=0.
    def rhs(t,y):
        enforce(t,y);h,R,L=y;a,c,N,Nn=geo(t);W=(R+L)/2;V=(R-L)/2
        Rp=np.zeros_like(R);Lm=np.zeros_like(L)
        Rp[:,1:-2]=(-2*R[:,:-3]-3*R[:,1:-2]+6*R[:,2:-1]-R[:,3:])/(6*dn);Rp[:,0]=(-3*R[:,0]+4*R[:,1]-R[:,2])/(2*dn);Rp[:,-2]=(R[:,-1]-R[:,-3])/(2*dn)
        Lm[:,2:-1]=(2*L[:,3:]+3*L[:,2:-1]-6*L[:,1:-2]+L[:,:-3])/(6*dn);Lm[:,1]=(L[:,2]-L[:,0])/(2*dn);Lm[:,-1]=(3*L[:,-1]-4*L[:,-2]+L[:,-3])/(2*dn)
        source=(Nn-3*N*c/a)*V-3*N/a*W-N*k*k/a**2*h
        r=N*Rp+source+Nn*W;l=-N*Lm+source-Nn*W
        r[:,-1]=0;l[:,0]=0
        return np.array([N*W,r,l])
    def obs(t,y):
        enforce(t,y);h,R,L=y;a,c,N,_=geo(t);W=(R+L)/2;V=(R-L)/2;sp=k*k*h*h/a**2
        mass=simpson(a**3*(c*(W*W+V*V+sp)+2*W*V)/6,x=n,axis=-1)
        flux=t**3*(-W[:,0]**2-V[:,0]**2+sp[:,0]-2*np.sqrt(1+t*t)*W[:,0]*V[:,0])/6
        return mass,flux,h[:,0].copy(),W[:,0].copy(),np.max(abs(h[:,-1]))
    times=1+dt*np.arange(steps+1); hist=[obs(1.,y)]
    for t in times[:-1]:
        a=rhs(t,y);b=rhs(t+dt/2,y+dt*a/2);c=rhs(t+dt/2,y+dt*b/2);d=rhs(t+dt,y+dt*c)
        y+=dt*(a+2*b+2*c+d)/6;hist.append(obs(t+dt,y))
    mass,flux,h,ht,outer=map(np.array,zip(*hist))
    if sample_n is None:return times,mass,flux,h,ht,outer
    # Actual final interior history jets at fixed GN time and normal.
    from scipy.interpolate import CubicSpline
    if not 0<sample_n<.5:raise ValueError('interior sample only')
    enforce(final,y);a,c,N,Nn=geo(final);U,R,L=y;W=(R+L)/2;V=(R-L)/2
    Wn=CubicSpline(n,W,axis=1)(sample_n,1);Vn=CubicSpline(n,V,axis=1)(sample_n,1)
    get=lambda arr:CubicSpline(n,arr,axis=-1)(sample_n)
    U0,W0,V0=map(get,(U,W,V));aa,cc,NN,NNn=map(get,(a,c,N,Nn));Nt=NN*(aa/cc-final/np.sqrt(1+final*final))/np.sqrt(1+final*final)
    Wt=NN*Vn+(NNn-3*NN*cc/aa)*V0-3*NN/aa*W0-NN*k[:,0]**2/aa**2*U0
    gn=np.stack((U0,NN*W0,V0,Nt*W0+NN*Wt,NNn*W0+NN*Wn,Vn),axis=1)
    return times,mass,flux,h,ht,outer,gn


def run(cutoff=80,nodes=12,cells=512):
    r,w=roots_legendre(nodes);k=cutoff*(r+1)/2;weight=w*cutoff/2*k*k/(5*np.pi**2)
    t,M,F,H,Ht,O=evolve(k,coefficient(k),cells);m=M@weight;f=F@weight;mi=cumulative_trapezoid(f,t,initial=0.)
    defect=np.max(abs(m-mi))/np.max(abs(m)); assert np.all(np.isfinite(m)) and m[-1]>0
    print('cutoff,nodes,cells',cutoff,nodes,cells,'mass',m[-1],'integrated flux defect',defect,'outer trace',max(O),flush=True)
    return m[-1],defect,H[-1]

if __name__=='__main__':
    for cells in (128,256,512,1024):run(cells=cells)
    for cutoff,nodes in ((80,24),(120,24),(160,32),(240,48),(320,64)):run(cutoff,nodes,1024)
