"""Direct GF(3) similitude compiler and standalone JSON streaming decoder.
The scalar gauge is an explicit input, not determined by quotient covariance.
"""
import json
from itertools import product
import numpy as np


def points(n):
    return np.array(list(product(range(3), repeat=n)), dtype=np.int64).reshape(3**n,n)


def rank(A):
    A=np.asarray(A,dtype=np.int64).copy()%3; k=0
    for j in range(A.shape[1]):
        p=next((i for i in range(k,len(A)) if A[i,j]),None)
        if p is None: continue
        A[[k,p]]=A[[p,k]]; A[k]=A[k]*A[k,j]%3
        for i in range(len(A)):
            if i!=k: A[i]=(A[i]-A[i,j]*A[k])%3
        k+=1
    return k


def compile_shape(A,lam,s):
    """Compile support and phase (input phase s); no operator matrix is used."""
    A=np.asarray(A,dtype=np.int64)%3; n=len(A)//2
    if not 1<=n<=8 or A.shape!=(2*n,2*n) or lam not in (1,2) or s not in (1,2):
        raise ValueError('source shape/phase')
    I=np.eye(n,dtype=np.int64); Z=np.zeros_like(I); C=np.block([[Z,Z],[I,Z]])
    J=C.T-C
    if np.any((A.T@J@A-lam*J)%3): raise ValueError('not a similitude')
    E=(A.T@C@A-lam*C)%3; a,b=A[:n,:n],A[:n,n:]; c,d=A[n:,:n],A[n:,n:]
    inds=[]
    for j in range(n):
        if rank(b[:,inds+[j]])>len(inds): inds.append(j)
    B=b[:,inds]; D=d[:,inds]; r=len(inds); X=points(n)
    ker=X[np.all(X@b.T%3==0,axis=1)]
    qker=2*np.sum((ker@E[n:,n:])*ker,axis=1)%3
    good=np.ones(len(X),dtype=bool)
    for t,q in zip(ker,qker): good &= (X@(d@t)+q)%3==0
    if good.sum()!=3**r: raise ValueError('vacuum coset size')
    y0=X[np.flatnonzero(good)[0]]; sout=s*lam%3
    # Q=sout*(q(x,0)+q(0,Lt)+(D t).y0+(c x).(y0+B t)).
    H=np.block([[2*E[:n,:n],c.T@B],[np.zeros((r,n),dtype=np.int64),2*E[n:,n:][np.ix_(inds,inds)]]])*sout%3
    linear=np.r_[c.T@y0,D.T@y0]*sout%3
    return dict(rank=r,a=a.tolist(),B=B.tolist(),origin=y0.tolist(),constant=0,linear=linear.tolist(),square=np.diag(H).tolist(),cross=[int((H[i,j]+H[j,i])%3) for i in range(n+r) for j in range(i+1,n+r)])


def load(payload):
    R=json.loads(payload); n=len(R['origin']); r=R['rank']; m=n+r
    if type(r)!=int or not 0<=r<=n or not 1<=n<=8: raise ValueError('rank/dimension')
    def trits(v,shape):
        arr=np.asarray(v,dtype=object)
        if arr.shape!=shape or any(type(x)!=int or x not in (0,1,2) for x in arr.flat): raise ValueError('invalid trits')
        return arr.astype(np.int64)
    for k,shape in [('a',(n,n)),('B',(n,r)),('origin',(n,)),('linear',(m,)),('square',(m,)),('cross',(m*(m-1)//2,))]: trits(R[k],shape)
    trits(R['constant'],())
    if rank(np.asarray(R['B']).reshape(n,r))!=r: raise ValueError('dependent support')
    g,h,d=R['scalar']
    if any(type(v)!=int for v in (g,h,d)) or d<=0 or (g*g-g*h+h*h)*3**r!=d*d: raise ValueError('scalar norm')
    return R


def columns(R):
    n=len(R['origin']); r=R['rank']; X=points(n); T=points(r)
    a,B,y0=map(lambda z:np.asarray(z,dtype=np.int64),(R['a'],R['B'],R['origin'])); powers=3**np.arange(n-1,-1,-1)
    lin=np.asarray(R['linear']); sq=np.asarray(R['square']); cross=R['cross']; g,h,_=R['scalar']
    roots=np.array([(g,h),(-h,g-h),(h-g,-g)],dtype=object)
    for j,x in enumerate(X):
        U=np.column_stack((np.tile(x,(len(T),1)),T)); y=((y0+a@x+T@B.T)%3)@powers
        q=(R['constant']+U@lin+(U*U)@sq)%3; k=0
        for i in range(n+r):
            for l in range(i+1,n+r): q=(q+cross[k]*U[:,i]*U[:,l])%3; k+=1
        yield j,y,roots[q].T


def apply(R,vector,adjoint=False):
    """Exact vector numerator and common denominator, no dense matrix.
    Python integer coefficients avoid overflow; O(N*3^r) streamed entries.
    """
    N=3**len(R['origin']); v=np.asarray(vector,dtype=object)
    if v.shape!=(2,N) or any(type(x)!=int for x in v.flat): raise ValueError('integer pair vector required')
    out=np.zeros((2,N),dtype=object)
    for j,y,(p,t) in columns(R):
        if adjoint:
            p,t=p-t,-t; u,w=v[:,y]; out[:,j]=[sum(p*u-t*w),sum(p*w+t*u-t*w)]
        else:
            u,w=v[:,j]; out[0,y]+=p*u-t*w; out[1,y]+=p*w+t*u-t*w
    return out,R['scalar'][2]
