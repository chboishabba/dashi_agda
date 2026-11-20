"""C3 tensor butterfly consumer of toe_cyclotomic_operator records.
Source schedule donor: MLKEMButterflyStageLocalityInvariantExact (radix two only).
C3 arithmetic donor: C3FourierConjugationExact / TriadicDepthOneCharacters.
"""
import numpy as np
from toe_cyclotomic_operator import points,rank

def root(v,k):
    a,b=v
    return [(a,b),(-b,a-b),(b-a,-a)][int(k)%3]

def butterfly(v,r):
    v=list(v); N=3**r
    for axis in range(r):
        stride=3**axis
        for base in range(0,N,3*stride):
            for i in range(stride):
                ids=[base+i+j*stride for j in range(3)]; old=[v[j] for j in ids]
                for k,j in enumerate(ids):
                    terms=[root(x,k*l) for l,x in enumerate(old)]
                    v[j]=tuple(map(sum,zip(*terms)))
    return v

def plan(R):
    n=len(R['origin']); r=R['rank']; X=points(n); U=points(r); N=len(X); pow3=3**np.arange(n-1,-1,-1); rp=3**np.arange(r-1,-1,-1)
    a=np.array(R['a']); B=np.array(R['B'],dtype=np.int64).reshape(n,r); y0=np.array(R['origin']); offsets=U@B.T%3
    off={tuple(v):i for i,v in enumerate(offsets)}
    groups={}
    for j,x in enumerate(X):
        y=(y0+a@x)%3; key=int((((y+offsets)%3)@pow3).min()); groups.setdefault(key,[]).append(j)
    def Q(x,t):
        v=np.r_[x,t]; q=R['constant']+v@R['linear']+(v*v)@R['square']; k=0
        for i in range(n+r):
            for j in range(i+1,n+r): q+=R['cross'][k]*v[i]*v[j]; k+=1
        return int(q%3)
    for ids in groups.values():
        if len(ids)!=3**r: raise ValueError('input block size')
        x0=X[ids[0]]; H=[]
        for j in ids:
            v=(X[j]-x0)%3
            if rank(np.array(H+[v]).T)>len(H): H.append(v)
        if len(H)!=r: raise ValueError('input affine block')
        H=np.array(H,dtype=np.int64).reshape(r,n).T; xs=(x0+U@H.T)%3; ybase=(y0+a@x0)%3; ys=(ybase+offsets)%3
        def q(v,w):
            x=(x0+H@v)%3; t=U[off[tuple((B@w-a@(H@v))%3)]]; return Q(x,t)
        zero=np.zeros(r,dtype=int); E=np.eye(r,dtype=int); q0=q(zero,zero)
        cross=np.array([[(q(v,w)-q(v,zero)-q(zero,w)+q0)%3 for v in E] for w in E],dtype=int).reshape(r,r)
        if rank(cross)!=r: raise ValueError('degenerate mixed phase')
        pre=[q(v,zero) for v in U]; post=[(q(zero,w)-q0)%3 for w in U]; freq=(U@cross%3)@rp
        yield xs@pow3,ys@pow3,pre,post,freq

def apply_fast(R,vector):
    N=3**len(R['origin']); r=R['rank']; out=np.zeros((2,N),dtype=object); g,h,d=R['scalar']
    for xi,yi,pre,post,freq in plan(R):
        v=butterfly([root(tuple(vector[:,j]),k) for j,k in zip(xi,pre)],r)
        for y,k,f in zip(yi,post,freq):
            a,b=root(v[f],k); out[:,y]=[a*g-b*h,a*h+b*g-b*h]
    return out,d
