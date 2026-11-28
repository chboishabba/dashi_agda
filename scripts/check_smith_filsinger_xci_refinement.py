"""Numerical diagnostics, same piecewise-constant source and fixed physical bin duration."""
import json
import numpy as np
from scipy.linalg import expm
from numpy.polynomial.legendre import leggauss
from check_smith_filsinger_xci_spectral import system, P, Y, G, S, q
A,B,M=map(lambda x:np.array(x,dtype=float),system()); Y=float(Y); G=float(G)
P=np.array([np.array(a,dtype=float).ravel() for a in P]); R=np.array([[20,-21],[21,20]])/29
inner=np.array([R@np.array([P[(j-1)%4,0],P[j,1]]) for j in range(4)])

def run(p,k,method):
    h=.1/k; n=len(A); I=np.eye(n); source=np.repeat(p,k,axis=0)
    if method=='midpoint':
        K=np.linalg.inv(I-h*A/2); T=2*K-I; D=h*K@B*(2*Y)
    else:
        aug=np.zeros((n+2,n+2)); aug[:n,:n]=A;aug[:n,n:]=B*(2*Y)
        E=expm(h*aug); T=E[:n,:n]; D=E[:n,n:]
        xs,ws=leggauss(40); Q=[(w*h/2,expm((x+1)*h/2*aug)[:n,:]) for x,w in zip(xs,ws)]
    v=np.zeros(n)
    for a in source:v=T@v+D@a
    mon=np.linalg.matrix_power(T,len(source)); z0=np.linalg.solve(I-mon,v)
    def cycle(z):
        inc=ref=term=ohm=rel=0.; start=z.copy()
        for a in source:
            z1=T@z+D@a; inc+=h*Y*(a@a)
            points=[(h,(z+z1)/2)] if method=='midpoint' else [(w,F@np.r_[z,a]) for w,F in Q]
            for w,mid in points:
                e=mid[:2];vel=mid[6:8];b=e-a
                ref+=w*Y*(b@b);term+=w*G*e[1]**2;ohm+=w*.2*(e@e);rel+=w*4/9*(vel@vel)
            z=z1
        storage=(z@M@z-start@M@start)/2
        return z,dict(eta=term/inc,incident=inc,reflected=ref,terminal=term,storage=storage,residual=inc-ref-term-ohm-rel-storage)
    z,period=cycle(z0);cold,first=cycle(np.zeros(n)); results={}
    for i in (1,100,1000,10000):
        c=z0-np.linalg.matrix_power(mon,i)@z0
        results[str(i)]=float(np.linalg.norm(c-z0)/np.linalg.norm(z0))
    return dict(k=k,method=method,rho=float(max(abs(np.linalg.eigvals(mon)))),period=period,first_cycle=first,cold_mismatch=results)

if __name__=='__main__':
    out={name:[run(p,k,'midpoint') for k in (1,2,4,8,16,32)]+[run(p,1,'zoh')] for name,p in [('baseline',P),('delay_mixer_inner',inner)]}
    print(json.dumps(out,indent=2))
