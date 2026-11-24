import numpy as np
import sympy as sp

def operators(n,h,b):
    z=b+h*np.arange(n); H=np.full(n,h); H[[0,-1]]=h/2
    D=np.zeros((n,n)); D[0,:2]=[-1,1]; D[-1,-2:]=[-1,1]
    for j in range(1,n-1): D[j,j-1]=-0.5; D[j,j+1]=0.5
    D/=h
    root=z**(-1.5); B=H*z**(-3)
    C=D*root[None,:]/root[:,None]+np.diag(1.5/z)-D
    adj=C.T*B[None,:]/B[:,None]
    return D,C,adj,B

def main():
    v,p,m=sp.symbols('v p m'); W=((1+v)*p+(1-v)*m)/2; N=(p-m)/2
    assert sp.expand((1+v)*p*p/2+(1-v)*m*m/2-W**2-(1-v*v)*N**2)==0
    rng=np.random.default_rng(369); count=0; worst=0.; transport=0.; norm=0.
    for t in (1,2,12):
      v=-1/np.sqrt(1+t*t); s=1-v*v
      for h in (.012,.009,.006):
       for n in (3,7,13):
        D,C,A,B=operators(n,h,1/t)
        norm=max(norm,np.linalg.norm(np.sqrt(B)[:,None]*C/np.sqrt(B)[None,:],2))
        for _ in range(4):
         W,N=rng.normal(size=(2,n)); dw=s*A@N; dn=-C@W
         e=abs(np.dot(B*W,dw)+s*np.dot(B*N,dn)); worst=max(worst,e)
         assert e<1e-9
         # original constraint source plus signed compensator
         F=C@W; boundary=np.zeros(n); boundary[[0,-1]]=rng.normal(size=2)
         transport=max(transport,np.max(abs(F+boundary+dn-boundary)))
         assert np.allclose(F+boundary+dn,boundary,atol=1e-12)
         assert np.allclose(F+boundary-F,boundary,atol=1e-12)
         count+=1
    print(dict(cases=count,energy_residual=worst,transport_residual=transport,max_sample_operator_norm=norm))
if __name__=='__main__': main()
