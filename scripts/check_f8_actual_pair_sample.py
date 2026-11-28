"""Actual original-source scalar/vector/TT bulk forcing at a nonzero Fourier direction.
Finite-band point diagnostic, not full history, constraint compatibility or convergence.
"""
import numpy as np
from scipy.special import roots_legendre
from scipy.interpolate import CubicSpline
from check_f8_characteristic_history import coefficient,evolve
from check_f8_full_pair_source import ordered,jets,split


def transform(t,n,g):
    """GN (H,Ht,Hn,Htt,Htn,Hnn) -> Poincare (H,HT,Hz,HTT,HTz,Hzz)."""
    r=np.sinh(np.arcsinh(t)-n);z=1/r;B=np.sqrt(1+z*z);c=np.sqrt(1+t*t)
    D=np.array([[c,c*z/B],[1,B/z]])
    H,Ht,Hn,Htt,Htn,Hnn=g
    v=np.array([Ht,Hn]);M=np.array([[Htt,Htn],[Htn,Hnn]])
    d=D.T@v;dd=D.T@M@D+Ht*np.array([[t,t*z/B],[t*z/B,t*(z/B)**2+c/B**3]])+Hn*np.diag([0.,-1/(z*z*B)])
    return z,np.array([H,*d,dd[0,0],dd[0,1],dd[1,1]])


def run(cutoff=80,nodes=6,histories=16,cells=512,t=1.035,n=.015,k=30.):
    # Generic direction, rotate to the x-axis without changing physical Q.
    u=np.array([1.,2.,3.]);u/=np.linalg.norm(u);v=np.cross(u,[0.,0.,1.]);v/=np.linalg.norm(v);R=np.column_stack((u,v,np.cross(u,v)));Q=R.T@np.diag([0.,1.,-1.])@R
    kh=cutoff*(1-np.cos(np.linspace(0,np.pi,histories)))/2
    gn=evolve(kh,np.ones_like(kh),cells,t,sample_n=n)[-1]
    a,w=roots_legendre(nodes);ps=cutoff*(a+1)/2;pw=w*cutoff/2
    interp=CubicSpline(kh,gn,axis=0);I=np.eye(3);axis=np.array([k,0.,0.]);out=np.zeros((5,5),complex)
    def E(p):
        P=I-np.outer(p,p)/(p@p);return P@Q@P-P*np.trace(P@Q)/2
    for p,wp in zip(ps,pw):
        lo=abs(k-p);hi=min(k+p,cutoff)
        if hi<=lo:continue
        for q,wq in zip(lo+(hi-lo)*(a+1)/2,(hi-lo)*w/2):
            z,gp=transform(t,n,interp(p)*coefficient(np.array([p]))[0]);_,gq=transform(t,n,interp(q)*coefficient(np.array([q]))[0])
            c=(k*k+p*p-q*q)/(2*k*p);r=p*np.sqrt(max(0.,1-c*c));ang=2*np.pi*np.arange(16)/16
            for ph in ang:
                P=np.array([p*c,r*np.cos(ph),r*np.sin(ph)]);V=axis-P
                out+=wp*wq*p*q/(4*np.pi**2*k*len(ang))*ordered(jets(P,E(P),*gp),jets(V,E(V),*gq),z)
    defect=np.max(abs(out-out.T));out=(out+out.T)/2
    S,perp,J=split(out,axis,z);TT=out[2:4,2:4]-np.eye(2)*np.trace(out[2:4,2:4])/2
    result=[np.linalg.norm(S),abs(perp),np.linalg.norm(J),np.linalg.norm(TT)]
    assert all(np.isfinite(result)) and min(result)>0
    print('actual point cutoff,nodes,histories,cells',cutoff,nodes,histories,cells,'scalar,perp,vector,TT norms',result,'raw symmetry defect',defect,flush=True)
    return result

if __name__=='__main__':
    run(nodes=4,histories=12,cells=256);run(nodes=6,histories=16,cells=512)
