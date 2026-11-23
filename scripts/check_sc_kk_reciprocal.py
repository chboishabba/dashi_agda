"""Reciprocal reduced Maxwell–TDGL / scalar field Hamiltonian fixture.
Dimensionless, transverse only; spatial scalar projection is selected, not 5D derivation.
Standard KK kinetic factor and GL theory; user coherent braking hypothesis;
Filsinger signed energy accounting. New numerical synthesis.
"""
import numpy as np
from scipy.linalg import null_space
from scipy.integrate import solve_ivp

def run(g=.2,m=.2,quartic=0.,dx=.25,tol=2e-10,N=6,freq=4.):
    edges=[]; rot=[]; idx={}
    for i in range(N):
        for j in range(N):
            for di,dj in ((1,0),(0,1)):
                if i+di<N and j+dj<N:
                    idx[i,j,di,dj]=len(edges); edges.append((i*N+j,(i+di)*N+j+dj)); rot.append((-(j-(N-1)/2) if di else i-(N-1)/2)/2)
    t,h=np.array(edges).T; n=N*N; D=np.zeros((len(t),n)); D[np.arange(len(t)),t]=-1; D[np.arange(len(t)),h]=1
    C=np.zeros(((N-1)**2,len(t)))
    for i in range(N-1):
        for j in range(N-1): C[i*(N-1)+j,[idx[i,j,1,0],idx[i+1,j,0,1],idx[i,j+1,1,0],idx[i,j,0,1]]]=[1,1,-1,-1]
    assert not np.any(C@D)
    Q=null_space(D.T); R=C@Q; k=Q.shape[1]; rot=np.array(rot); drive=Q.T@rot; drive/=np.linalg.norm(drive)
    x=np.arange(-32+dx,32,dx); l=len(x); w=np.exp(-x*x/2); w/=dx*w.sum(); damp=2*np.maximum((abs(x)-24)/8,0)**2
    def unpack(z):
        return z[:n]+1j*z[n:2*n],z[2*n:2*n+k],z[2*n+k:2*n+2*k],z[2*n+2*k:2*n+2*k+l],z[2*n+2*k+l:-3]
    def calc(z,r):
        p,A,P,s,v=unpack(z); Z=np.exp(g*dx*(w@s)); B=R@A; E=P/Z
        U=np.exp(-1j*(Q@A+r*rot)); d=U*p[h]-p[t]; den=abs(p)**2
        F=np.sum(-den+den**2/2)+.4*np.vdot(d,d).real
        grad=(-1+den)*p; np.add.at(grad,t,-.4*d); np.add.at(grad,h,.4*np.conj(U)*d)
        j=.8*np.real(np.conj(d)*(-1j*U*p[h]))
        H=F+.5*(P@E+Z*(B@B))+dx*(.5*(v@v+m*m*(s@s))+quartic/4*np.sum(s**4)+.5*np.sum(np.diff(np.r_[0,s,0])**2)/dx**2)
        source=-g/2*Z*(B@B-E@E)*w
        return H,grad,j,Z,B,E,source
    def rhs(t,z,b,pump):
        r=.12-b*.08*min(t/10,1); rd=-b*.008 if t<10 else 0.
        _,grad,j,Z,B,E,source=calc(z,r); p,A,P,s,v=unpack(z); f=pump*.6*np.cos(freq*t)*drive
        dp=-grad; dP=-Q.T@j-Z*R.T@B-.15*E+f
        lap=(np.r_[s[1:],0]-2*s+np.r_[0,s[:-1]])/dx**2
        dv=lap-m*m*s-quartic*s**3-damp*v+source
        return np.r_[dp.real,dp.imag,E,dP,v,dv,j@rot*rd,E@f,2*np.vdot(grad,grad).real+.15*(E@E)+dx*np.dot(damp,v*v)]
    z=np.r_[np.ones(n),np.zeros(n+2*k+2*l+3)]
    def prep(t,z):
        dz=rhs(t,z,0,0); dz[-3-l:-3]-=unpack(z)[4]; return dz
    sol=solve_ivp(prep,(0,100),z,rtol=1e-8,atol=1e-10,max_step=.15); assert sol.success
    initial=sol.y[:,-1]; initial[-3:]=0; H0=calc(initial,.12)[0]; ts=np.linspace(0,20,401)
    out={}; waves={}
    for b,pump in ((0,0),(1,0),(0,1),(1,1)):
        sol=solve_ivp(lambda t,z:rhs(t,z,b,pump),(0,20),initial,t_eval=ts,rtol=tol,atol=tol/100,max_step=.05); assert sol.success
        H=np.array([calc(z,.12-b*.08*min(t/10,1))[0] for t,z in zip(ts,sol.y.T)])
        Wb,Wr,L=sol.y[-3:]; err=max(abs(H-H0-Wb-Wr+L)); assert err<2e-6,err
        q=sol.y[2*n+2*k:2*n+2*k+l]; i=np.argmin(abs(x-5)); wave=(q[i+1]-q[i-1])/(2*dx); wave-=wave[0]; waves[b,pump]=wave
        out[b,pump]=np.array([Wb[-1],Wr[-1],L[-1],H[-1]-H0,err,max(abs(wave))])
    return out,max(abs(waves[1,1]-waves[1,0]-waves[0,1]+waves[0,0]))

if __name__=='__main__':
    for g,m,q in [(0,.2,0),(.2,.2,0),(.2,1,0),(.2,.2,10)]:
        a,i=run(g,m,q); print(g,m,q,{k:v.tolist() for k,v in a.items()},'interaction',i,flush=True)
        if g==0: assert all(v[-1]==0 for v in a.values())
    a,_=run(.2,.2,0,dx=.125); b,_=run(.2,.2,0,dx=.25,tol=2e-12); print('mesh refined',a[1,1], 'tight',b[1,1],flush=True)
