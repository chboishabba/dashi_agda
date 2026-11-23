"""Dimensionless finite TDGL + dynamical transverse Maxwell-link fixture.
Standard GL/link and Maxwell energy; user coherent braking hypothesis; Filsinger
signed ports. Open graph, projected transverse electric dynamics, neutralizing
longitudinal sector not solved. Not calibrated REBCO or exterior radiation.
"""
import numpy as np
from scipy.integrate import solve_ivp
from scipy.linalg import null_space

def model(N=6, capture=False):
    edges=[]; rot=[]; idx={}
    for i in range(N):
        for j in range(N):
            for di,dj in ((1,0),(0,1)):
                if i+di<N and j+dj<N:
                    idx[i,j,di,dj]=len(edges); edges.append((i*N+j,(i+di)*N+j+dj)); rot.append((-(j-(N-1)/2) if di else i-(N-1)/2)/2)
    t,h=np.array(edges).T; D=np.zeros((len(t),N*N)); D[np.arange(len(t)),t]=-1; D[np.arange(len(t)),h]=1
    C=np.zeros(((N-1)**2,len(t)))
    for i in range(N-1):
        for j in range(N-1):
            C[i*(N-1)+j,[idx[i,j,1,0],idx[i+1,j,0,1],idx[i,j+1,1,0],idx[i,j,0,1]]]=[1,1,-1,-1]
    assert np.max(abs(C@D))==0
    Q=null_space(D.T); rot=np.array(rot); drive=Q.T@rot; drive/=np.linalg.norm(drive)
    J=.4; gamma=1.; sigma=.15; n=N*N; k=Q.shape[1]
    def gl(p,A):
        U=np.exp(-1j*A); z=U*p[h]-p[t]; den=abs(p)**2
        F=np.sum(-den+den**2/2)+J*np.vdot(z,z).real
        g=(-1+den)*p; np.add.at(g,t,-J*z); np.add.at(g,h,J*np.conj(U)*z)
        j=2*J*np.real(np.conj(z)*(-1j*U*p[h])); return F,g,j
    def unpack(z): return z[:n]+1j*z[n:2*n],z[2*n:2*n+k],z[2*n+k:2*n+2*k]
    def calc(z,r):
        p,A,v=unpack(z); B=C@Q@A; F,g,j=gl(p,Q@A+r*rot)
        return F+(B@B+v@v)/2,g,j,B
    def rhs(t,z,b,pump):
        r=.12-b*.08*min(t/10,1); rd=-b*.008 if t<10 else 0.
        _,g,j,B=calc(z,r); _,A,v=unpack(z); f=pump*.6*np.cos(4*t)*drive
        dp=-g; dv=-Q.T@(j+C.T@B)-sigma*v+f
        return np.r_[dp.real,dp.imag,v,dv,j@rot*rd,v@f,2*np.vdot(g,g).real+sigma*(v@v)]
    z=np.r_[np.ones(n),np.zeros(n+2*k+3)]
    initial=solve_ivp(lambda t,z:rhs(t,z,0,0),(0,180),z,rtol=1e-10,atol=1e-12).y[:,-1]; initial[-3:]=0
    rng=np.random.default_rng(42); p,A,v=unpack(initial); chi=rng.normal(size=n); link=Q@A+.12*rot
    F,g,j=gl(p,link); F2,g2,j2=gl(p*np.exp(1j*chi),link+D@chi)
    assert abs(F-F2)<1e-10 and np.max(abs(g2-g*np.exp(1j*chi)))<1e-10 and np.max(abs(j-j2))<1e-10
    def run(b,pump,tol):
        ts=np.linspace(0,20,401); sol=solve_ivp(lambda t,z:rhs(t,z,b,pump),(0,20),initial,rtol=tol,atol=tol/100,t_eval=ts,max_step=.05); assert sol.success
        E0=calc(initial,.12)[0]; E=[]; inv=[]; rho=[]
        for t,z in zip(ts,sol.y.T):
            e,_,_,B=calc(z,.12-b*.08*min(t/10,1)); p,A,v=unpack(z); E.append(e); inv.append(2*(B@B-v@v)); rho.append(np.mean(abs(p)**2))
        Wb,Wr,diss=sol.y[-3:]; res=max(abs(np.array(E)-E0-Wb-Wr+diss)); assert res<2e-6
        if capture: traces[(b,pump)]=(ts,np.array(inv))
        return np.array([Wb[-1],Wr[-1],diss[-1],E[-1]-E0,res,max(abs(np.array(inv)-inv[0])),min(rho)])
    traces={}
    out={}
    for name,b,pump in [('hold',0,0),('brake',1,0),('rf',0,1),('combined',1,1)]:
        a=run(b,pump,1e-8); c=run(b,pump,1e-10); assert max(abs(a-c))<1e-5; out[name]=c; print(name,c)
    print('interaction',out['combined']-out['brake']-out['rf']+out['hold']); print('PASS gauge GL, curl grad, transverse dynamics, work ledger and tolerance checks')
    return traces if capture else out
if __name__=='__main__': model()
