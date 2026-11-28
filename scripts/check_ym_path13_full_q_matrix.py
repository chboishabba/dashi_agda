"""Full selected Path13 averaging operator and mixed jets, at identity.
Reuse exact CMP98 group/Lie jet regression. Reverse accumulation deposits
all positive and negative oriented fine-bond coordinates. No dense square
fine operator is formed. CMP99 pivot check on this same averaging matrix.
"""
import numpy as np
import sympy as S
from fractions import Fraction as F
from itertools import product
from check_ym_path13_full_mixed_jet import N, PAIRS, mul, conj, one, div, logjet, walkword, coarse, link, atfield
DEN=13*N**3
M=4
I=np.zeros((4,3,3),dtype=np.int64);I[0]=np.eye(3,dtype=np.int64)

def mm(a,b):
    shape=np.broadcast_shapes(a.shape,b.shape);out=np.zeros(shape,dtype=np.int64)
    aa=[int(np.max(np.abs(a[...,k,:,:]))) for k in range(M)]
    bb=[int(np.max(np.abs(b[...,k,:,:]))) for k in range(M)]
    for k,ps in enumerate(PAIRS[:M]):
        assert 3*sum(aa[i]*bb[j] for i,j in ps)<2**63
        for i,j in ps:out[...,k,:,:]+=a[...,i,:,:]@b[...,j,:,:]
    return out

def ad(y):
    x,z,w=np.moveaxis(y[...,1:],-1,0);r=np.zeros(y.shape[:-1]+(3,3),dtype=np.int64)
    r[...,0,1]=-2*w;r[...,0,2]=2*z;r[...,1,0]=2*w;r[...,1,2]=-2*x;r[...,2,0]=-2*z;r[...,2,1]=2*x
    return r

def rot(q):
    # Ad_q by literal quaternion conjugation, not the reduced log polynomial.
    r=np.empty(q.shape[:-1]+(3,3),dtype=np.int64)
    for j in range(3):
        e=np.zeros((4,4),dtype=np.int64);e[0,j+1]=1
        v=mul(mul(q,e),conj(q));assert np.all(v[...,0]==0);r[...,j]=v[...,1:]
    return r

def siteid(x):return ((x[:,0]*13+x[:,1])*13+x[:,2])*13+x[:,3]

def deposit(acc,site,offset,weight):
    q=one(site.shape[:-1],m=4);site=site.copy()
    for axis in range(4):
        direction=np.sign(offset[:,axis]);length=np.abs(offset[:,axis])
        for k in range(int(length.max())):
            active=length>k;neg=direction<0
            start=site.copy();start[:,axis]=(start[:,axis]-neg)%13
            u=link(start,axis)[...,:4,:];u[neg]=conj(u[neg]);u[~active]=one(m=4)
            qnext=mul(q,u);p=q.copy();p[neg]=qnext[neg]
            v=mm(weight,rot(p));v[neg]*=-1
            idx=siteid(start[active]);values=v[active]
            count=int(np.bincount(idx,minlength=N).max())
            assert int(np.max(np.abs(acc[:,axis])))+count*int(np.max(np.abs(values)))<2**63
            np.add.at(acc[:,axis],idx,values)
            q=qnext;site[:,axis]=(site[:,axis]+direction*active)%13
    return q,site

def calc(axis,offsets):
    start=np.zeros_like(offsets);minus,x=walkword(start,offsets);cross,xp=coarse(x,axis);center,plus=coarse(start[:1],axis)
    assert np.all(plus==0);assert np.array_equal(x,xp)
    minus=minus[:,:4];cross=cross[:,:4];center=center[:,:4]
    rel=mul(mul(minus,cross),conj(mul(center,minus)));ys=logjet(rel)
    X=ad(ys);J=I-div(X,2)+div(mm(X,X),12)
    # shared denominator N^2 for outer differential and adjoint exponential.
    Xbar=ad(ys.sum(axis=0));X2=mm(Xbar,Xbar)
    Dnum=N*N*I+N*div(Xbar,2)+div(X2,6)
    Adnum=N*N*I+N*Xbar+div(X2,2)
    C=rot(center);R=rot(rel);U=rot(minus)
    JR=mm(J,R)
    wminus=mm(Dnum,J-mm(JR,C))+N*N*(C-I)
    wcross=mm(Dnum,mm(J,U))
    wcenter=-mm(Dnum,JR.sum(axis=0))+N*Adnum
    acc=np.zeros((N,4,4,3,3),dtype=np.int64)
    deposit(acc,start,offsets,wminus)
    long=np.zeros_like(x);long[:,axis]=13
    deposit(acc,x,long,wcross)
    deposit(acc,start[:1],long[:1],wcenter)
    # At identity Q is exactly the uniform directional average.
    for d in range(4):
        expected=np.eye(3,dtype=np.int64)*(DEN//N if d==axis else 0)
        assert np.all(acc[:,d,0]==expected)
    # All columns independently contract to the previously executed mixed jet.
    sites=np.array(list(product(range(13),repeat=4)),dtype=np.int64)
    result=np.zeros((4,3),dtype=object)
    for d in range(4):
        A=atfield(sites,d,2)[:,1:]
        # multiply and sum using Python integers, no wrap-around.
        for k in range(4):
            for i in range(3):
                result[k,i]+=sum(int(u)*int(v) for u,v in zip(acc[:,d,k,i,:].flat,A.flat))
    return acc,np.array([F(int(v),DEN) for v in result.flat],dtype=object).reshape(4,3)

if __name__=='__main__':
    from check_ym_path13_full_mixed_jet import cert
    offsets=np.array(list(product(range(-6,7),repeat=4)),dtype=np.int64)
    pivots=[S.zeros(12) for _ in range(4)]
    rows=[]
    import math
    def normalize(A):
        g=math.gcd(DEN,int(np.gcd.reduce(A.flat)))
        return A//g,DEN//g
    for axis in range(4):
        A,r=calc(axis,offsets)
        assert np.array_equal(r,cert(axis)[:,1:])
        for m in range(4):
            for d in range(4):
                pivots[m][3*axis:3*axis+3,3*d:3*d+3]=S.Matrix(A[0,d,m].tolist())/DEN
        rows.append([normalize(A[:,:,m].transpose(2,0,1,3).reshape(3,-1)) for m in range(4)])
        print('PASS full Q matrix rows',3*axis,'..',3*axis+2,'columns',N*12,flush=True)
    p,ps,pt,pst=pivots;assert p==S.eye(12)/N
    g=p.inv();mix=S.trace(g*pst-g*pt*g*ps)
    print('PASS literal origin pivot P0=I/28561; det(P0)=',p.det(),flush=True)
    print('mixed log|det P|=',mix,'; delta pivot 2 Gamma_st contribution=',2*mix,flush=True)

    # Actual Gram measure response of the full Q (normalization independent of A).
    # Each dot product uses guarded int64 or Python arbitrary precision.
    gram=[S.zeros(12) for _ in range(4)]
    for i in range(4):
        for j in range(4):
            for k,ps in enumerate(PAIRS[:4]):
                block=S.zeros(3)
                for a,b in ps:
                    U,du=rows[i][a]; V,dv=rows[j][b]
                    bound=U.shape[1]*int(np.max(np.abs(U)))*int(np.max(np.abs(V)))
                    if bound<2**63:
                        dot=U@V.T
                        block+=S.Matrix(dot.tolist())/(du*dv)
                    else:
                        for u in range(3):
                            for v in range(3):
                                block[u,v]+=S.Rational(sum(int(x)*int(y) for x,y in zip(U[u],V[v])),du*dv)
                gram[k][3*i:3*i+3,3*j:3*j+3]=block
    M0,Ms,Mt,Mst=gram
    assert M0==S.eye(12)/N
    assert all(m==m.T for m in gram)
    G=M0.inv();mixM=S.trace(G*Mst-G*Mt*G*Ms)
    print('actual full Q Gram logdet mixed response =',mixM,flush=True)
    print('induced minus delta 2 Gamma_st =',-mixM,flush=True)
    assert mixM!=0
    print('PASS actual Q moving Gram measure at flat background',flush=True)
