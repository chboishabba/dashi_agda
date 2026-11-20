"""Exact finite trace via cyclic number-theoretic transforms and CRT.
No floating-point rounding is used for the Gaussian result. Reuses the
literal Path13 Wilson+divergence Hessian and Q jets, not a source beta theorem.
"""
import numpy as np
import sympy as S
from math import gcd
from check_ym_path13_hessian_gaussian import (N,L,shape,axes,shift,green,build,qjets,actual_trace)

neg=np.r_[0,np.arange(L-1,0,-1)]
def negfreq(f):
    for i in axes:f=np.take(f,neg,axis=i)
    return f
class Transform:
    def __init__(self,p):
        self.p=p;r=pow(int(S.primitive_root(p)),(p-1)//L,p)
        assert pow(r,L,p)==1 and r!=1 and L*(p-1)**2 < 2**63
        self.W=np.array([[pow(r,i*j,p) for j in range(L)] for i in range(L)],dtype=np.int64)
        ri=pow(r,-1,p);il=pow(L,-1,p)
        self.V=np.array([[il*pow(ri,i*j,p)%p for j in range(L)] for i in range(L)],dtype=np.int64)
    def ntt(self,f,inverse=False):
        W=self.V if inverse else self.W;p=self.p
        a=np.asarray(f,dtype=np.int64)%p
        for i in axes:
            x=np.moveaxis(a,i,0);b=(W@x.reshape(L,-1))%p
            a=np.moveaxis(b.reshape(x.shape),0,i)
        return a

def primes(bound):
    p=100000000;prod=1;out=[]
    while prod<=2*bound:
        p=p+(1-p)%L
        while not S.isprime(p):p+=L
        out.append(p);prod*=p;p+=1
    return out

def add_crt(old,m,new,p):
    if m==1:return new.copy()
    # object integers only if the combined modulus would overflow int64
    corr=((new-np.asarray(old%p,dtype=np.int64))%p)*pow(m,-1,p)%p
    if m*p<2**63:return old+m*corr
    return old.astype(object)+m*corr.astype(object)

def signed(a,m):
    return np.where(a>m//2,a-m,a)

def exact_bubble(H,G,d):
    # All first-jet color blocks are skew, so tr xy = -2 dot of 3 entries.
    entries={};bound={}
    for (mu,nu,off),h in H.items():
        assert np.array_equal(h[:,1:3],-h[:,1:3].swapaxes(-1,-2))
        f=h[:,1:3, [0,0,1],[1,2,2]]
        if np.any(f):entries.setdefault((mu,nu),[]).append((off,f))
    for (mu,nu),ls in entries.items():
        for a,f in ls:
            for b,g in entries.get((nu,mu),[]):
                k=(a,b);bound[k]=bound.get(k,0)+6*N*int(abs(f[:,0]).max())*int(abs(g[:,1]).max())
    ps=primes(max(bound.values()));print('bubble correlation CRT primes',ps,'groups',len(bound),'bound',max(bound.values()),flush=True)
    acc={};mod=1
    for p in ps:
        t=Transform(p);freq={}
        for key,ls in entries.items():
            freq[key]=[(off,negfreq(t.ntt(f[:,0].reshape(shape+(3,)))),t.ntt(f[:,1].reshape(shape+(3,)))) for off,f in ls]
        groups={}
        for (mu,nu),ls in freq.items():
            for a,fs,_ in ls:
                for b,_,ft in freq.get((nu,mu),[]):
                    k=(a,b);c=(-2*(fs*ft).sum(axis=-1))%p
                    if k in groups:groups[k]=(groups[k]+c)%p
                    else:groups[k]=c
        for k,f in groups.items():
            z=t.ntt(f,True).reshape(N)
            acc[k]=add_crt(acc.get(k),mod,z,p)
        mod*=p;print('PASS full bubble correlations mod',p,flush=True)
    num=0
    for (a,b),f in acc.items():
        f=signed(f,mod);assert max(abs(int(v)) for v in f)<=bound[a,b]
        kernel=shift(G,b)*shift(G,tuple(-x for x in a))
        num+=sum(int(x)*int(y) for x,y in zip(f,kernel))
    return S.Rational(num,d*d)

def exact_cross(V,q,G,d,qd):
    # tr Q G V, Q=(coarse,site,fine), V=(site,fine,coarse).
    # Q coefficient normalization before CRT; correlation sum over all 144 channels.
    g=gcd(qd,int(np.gcd.reduce(q.flat)));q=q//g;qd//=g
    q=np.transpose(q,(1,2,0)).reshape(shape+(144,));v=V.reshape(shape+(144,))
    # q must align fine,coarse with V.  CRT bound on each displacement.
    bound=N*sum(int(abs(q[...,i]).max())*int(abs(v[...,i]).max()) for i in range(144))
    ps=primes(bound);acc=None;m=1
    for p in ps:
        t=Transform(p);c=np.zeros(shape,dtype=np.int64)
        # chunk columns to bound memory and sum of products
        for j in range(0,144,12):
            f=negfreq(t.ntt(q[...,j:j+12]));h=t.ntt(v[...,j:j+12]);c=(c+(f*h).sum(axis=-1))%p
        acc=add_crt(acc,m,t.ntt(c,True).reshape(N),p);m*=p
    corr=signed(acc,m);assert max(abs(int(v)) for v in corr)<=bound
    num=sum(int(x)*int(y) for x,y in zip(corr,G))
    print('cross correlation CRT primes',ps,'bound',bound,flush=True)
    return S.Rational(num,d*qd)

def exact_constraint(H,q,qd,G,d):
    V=np.zeros((2,N,12,12),dtype=np.int64)
    for (mu,nu,off),h in H.items():
        for k in range(2):V[k,:,3*mu:3*mu+3,3*nu:3*nu+3]+=h[:,k+1]
    qsum=[S.Matrix([[sum(int(x) for x in q[k,i,:,j]) for j in range(12)] for i in range(12)])/qd for k in range(4)]
    assert qsum[0]==S.eye(12)
    base=2*S.trace(qsum[3]-qsum[1]*qsum[2]);c=[exact_cross(V[k],q[2-k],G,d,qd) for k in range(2)]
    print('exact cross',c, 'approx',list(map(float,c)),flush=True)
    return base-2*sum(c)

if __name__=='__main__':
    p=primes(1)[0];t=Transform(p);v=np.arange(N,dtype=np.int64).reshape(shape)
    assert np.array_equal(v,t.ntt(t.ntt(v),True));print('PASS NTT inversion',flush=True)
    G,d=green();H=build();tad=S.Rational(actual_trace(H,G,d),d)
    bub=exact_bubble(H,G,d);print('exact bubble',bub,'approx',float(bub),flush=True)
    q,qd=qjets();cor=exact_constraint(H,q,qd,G,d)
    result=tad-bub+cor
    print('exact moving constraint',cor,'approx',float(cor),flush=True)
    print('exact finite 2 Gamma_st delta',result,'approx',float(result),flush=True)
    assert abs(float(result)-5297956.1745270025)<1e-6
    print('PASS exact CRT reconstruction agrees with independently evaluated Fourier trace',flush=True)
