"""Dimensionless finite gauge-covariant TDGL film, prescribed links.
Not calibrated YBCO or self-consistent Maxwell. Standard GL/link discretization;
user's coherent braking hypothesis; Filsinger-style signed work accounting.
"""
import numpy as np
from scipy.integrate import solve_ivp

N=8; J=.4; gamma=1.; a=-1.; b=1.
x,y=np.meshgrid(np.arange(N)-(N-1)/2,np.arange(N)-(N-1)/2,indexing='ij')
i,j=np.indices((N,N)); tail=[]; head=[]; rot=[]; rf=[]
for axis in (0,1):
    mask=(i<N-1) if axis==0 else (j<N-1)
    tail.extend((i*N+j)[mask]); head.extend(((i+(axis==0))*N+j+(axis==1))[mask]); rot.extend((-y if axis==0 else x)[mask]/2); rf.extend(np.full(mask.sum(),1. if axis==0 else 0.))
tail,head=np.array(tail),np.array(head); rot,rf=np.array(rot),np.array(rf)

def drive(t,brake,pump):
    r=.12-brake*.08*min(t/10,1); rd=-brake*.008 if t<10 else 0.
    return r*rot+pump*.12*np.sin(7*t)*rf,rd*rot+pump*.84*np.cos(7*t)*rf

def evaluate(p,A):
    U=np.exp(-1j*A); z=U*p[head]-p[tail]; dens=abs(p)**2
    energy=np.sum(a*dens+b*dens**2/2)+J*np.vdot(z,z).real
    g=(a+b*dens)*p
    np.add.at(g,tail,-J*z); np.add.at(g,head,J*np.conj(U)*z)
    dA=2*J*np.real(np.conj(z)*(-1j*U*p[head]))
    return energy,g,dA

def run(brake,pump,tol):
    p=np.ones(N*N,complex)
    def relax(t,z): return -gamma*evaluate(z,drive(0,0,0)[0])[1]
    p=solve_ivp(relax,(0,60),p,rtol=1e-10,atol=1e-12).y[:,-1]
    A,_=drive(0,0,0); E0=evaluate(p,A)[0]
    def rhs(t,z):
        p=z[:-3]; A,Ad=drive(t,brake,pump); E,g,dA=evaluate(p,A)
        rd=-brake*.008 if t<10 else 0.; pd=pump*.84*np.cos(7*t)
        return np.r_[-gamma*g,np.dot(dA,rot)*rd,np.dot(dA,rf)*pd,2*gamma*np.vdot(g,g).real].astype(complex)
    z=np.r_[p,0,0,0].astype(complex); ts=np.linspace(0,20,401)
    sol=solve_ivp(rhs,(0,20),z,rtol=tol,atol=tol/100,t_eval=ts,max_step=.035)
    assert sol.success
    energies=[]; currents=[]; density=[]
    for t,z in zip(ts,sol.y.T):
        E,g,dA=evaluate(z[:-3],drive(t,brake,pump)[0]); energies.append(E); currents.append(np.linalg.norm(dA)); density.append(np.mean(abs(z[:-3])**2))
    Wb,Wr,Q=sol.y[-3:].real; residual=np.array(energies)-E0-Wb-Wr+Q
    return np.array([Wb[-1],Wr[-1],Q[-1],energies[-1]-E0,max(abs(residual)),max(currents),min(density)]),sol

def main():
    rng=np.random.default_rng(23); p=rng.normal(size=N*N)+1j*rng.normal(size=N*N); A=rng.normal(size=len(tail)); chi=rng.normal(size=N*N)
    E,g,d=evaluate(p,A); E2,g2,d2=evaluate(p*np.exp(1j*chi),A+chi[head]-chi[tail]); assert abs(E-E2)<1e-10; assert np.max(abs(g2-g*np.exp(1j*chi)))<1e-10; assert np.max(abs(d-d2))<1e-10
    eps=1e-6; k=9; Ap=A.copy(); Am=A.copy(); Ap[k]+=eps; Am[k]-=eps; assert abs((evaluate(p,Ap)[0]-evaluate(p,Am)[0])/(2*eps)-d[k])<1e-6
    results={}
    for name,bk,rfp in [('hold',0,0),('brake',1,0),('rf',0,1),('combined',1,1)]:
        v,_=run(bk,rfp,1e-8); w,_=run(bk,rfp,1e-10); assert w[4]<1e-6; assert max(abs(v[[0,1,2,3]]-w[[0,1,2,3]]))<1e-5; results[name]=w; print(name, w)
    interaction=results['combined']-results['brake']-results['rf']+results['hold']; print('factorial interaction',interaction); print('PASS gauge covariance, link-current derivative, four worlds, ledger and tolerance convergence')
if __name__=='__main__':main()
