"""Exact affine/quadratic codec of selected ATLAS operators; reuse composed owner."""
import json
from itertools import product
import numpy as np
import check_toe_atlas_composed as D
c=D.c; X=c.X; N=c.N

def fit(name,A,H,den):
    a,b=A[:6,:6],A[:6,6:]
    cols=[]
    for v in b.T:
        if c.rank(np.array(cols+[v]).T)>len(cols): cols.append(v)
    r=len(cols); B=np.array(cols,dtype=np.int64).reshape(r,6).T
    mask=(H[0]!=0)|(H[1]!=0)
    y0=X[np.flatnonzero(mask[:,0])[0]]
    seed=int(c.idx(y0)); g=tuple(int(h[seed,0]) for h in H)
    roots=[g,(-g[1],g[0]-g[1]),(g[1]-g[0],-g[0])]
    def value(u):
        x=u[:6]; t=u[6:]; y=(y0+a@x+B@t)%3
        return roots.index(tuple(int(h[c.idx(y),c.idx(x)]) for h in H))
    n=6+r; E=np.eye(n,dtype=np.int64); z=np.zeros(n,dtype=np.int64)
    const=value(z); lin=np.zeros(n,dtype=np.int64); sq=lin.copy(); cross=[]
    for i,e in enumerate(E):
        p=(value(e)-const)%3; q=(value(2*e)-const)%3
        sq[i]=(2*(p+q))%3; lin[i]=(p-sq[i])%3
    for i in range(n):
        for j in range(i+1,n):
            cross.append((i,j,(value(E[i]+E[j])-const-lin[i]-lin[j]-sq[i]-sq[j])%3))
    T=np.array(list(product(range(3),repeat=r)),dtype=np.int64).reshape(3**r,r)
    out=[np.zeros_like(h) for h in H]
    for j,x in enumerate(X):
        U=np.column_stack((np.tile(x,(len(T),1)),T)); y=c.idx(y0+x@a.T+T@B.T)
        phase=(const+U@lin+(U*U)@sq)%3
        for i,k,v in cross: phase=(phase+v*U[:,i]*U[:,k])%3
        assert len(set(y))==3**r
        for k in range(2): out[k][y,j]=np.array(roots)[phase,k]
    assert D.same(out,H)
    assert np.all(mask.sum(axis=0)==3**r) and np.all(mask.sum(axis=1)==3**r)
    assert (g[0]**2-g[0]*g[1]+g[1]**2)*3**r==den**2
    record=dict(name=name,rank=r,a=a.tolist(),B=B.tolist(),origin=y0.tolist(),scalar=[*g,den],constant=int(const),linear=lin.tolist(),square=sq.tolist(),cross=[int(v) for _,_,v in cross])
    size=len(json.dumps(record,separators=(',',':')).encode())
    print(name,'rank',r,'support',3**r,'record bytes',size,'dense exponent bytes',N*N, 'PASS')
    return record

if __name__=='__main__':
    M=c.inv(c.P)@c.m@c.P%3; R=c.inv(c.P)@c.r@c.P%3
    k=D.entrymul(D.k,(-1,-2))
    entries=[('adapted mirror',c.inv(c.Pa)@c.m@c.Pa%3,D.identity,1),('original mirror',M,D.S,D.sd),('rechart',c.A,k,27),('rotation',R,D.R,D.rd)]
    records=[]
    for name,A,H,den in entries:
        records.append(fit(name,A,H,den))
        records.append(fit(name+' conjugate',A,D.conj(H),den))
    print('PASS',len(records)*N*N,'complex coefficient positions; exact gauge retained')
