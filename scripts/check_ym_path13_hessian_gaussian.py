"""Wilson six-plane + covariant divergence quadratic form on full Path13.
Wilson 1974; Balaban CMP98/99/109. Left fluctuation exp(h)U, with background
exp(sB)exp(tC). Not an identification with the entire CMP109 source A or beta.
"""
import numpy as np
import sympy as S
from sympy.polys.matrices import DomainMatrix
from scipy.fft import fftn, ifftn
from itertools import product, combinations_with_replacement
from collections import Counter
from math import gcd
from check_ym_path13_full_mixed_jet import N, mul, conj, link
from check_ym_path13_full_q_matrix import calc, rot, mm, DEN
L=13; shape=(L,)*4; sites=np.array(list(product(range(L),repeat=4)),dtype=np.int64)
zero=(0,0,0,0); eye=np.eye(4,dtype=np.int64); E=np.eye(3,dtype=np.int64)
axes=(0,1,2,3)
def shift(a,d):
    return np.roll(a.reshape(shape+a.shape[1:]),tuple(-int(t) for t in d),axis=axes).reshape(a.shape)
def green():
    pts=list(combinations_with_replacement(range(7),4)); idx={p:i for i,p in enumerate(pts)};m=len(pts)
    def orbit(x):return tuple(sorted(min(t%L,(-t)%L) for t in x))
    M=[[0]*m for _ in pts];b=[0]*m
    for i,x in enumerate(pts):
        M[i][i]=8
        for e in eye:
            for sign in [-1,1]:M[i][idx[orbit(np.asarray(x)+sign*e)]]-=1
        b[i]=N*int(i==0)-1
    cnt=Counter(orbit(x) for x in product(range(L),repeat=4));M[0]=[cnt[x] for x in pts];b[0]=0
    A=DomainMatrix.from_Matrix(S.Matrix(M)).convert_to(S.ZZ);B=DomainMatrix.from_Matrix(S.Matrix(b)).convert_to(S.ZZ)
    x,d=A.solve_den(B);vals=[int(t) for t in x.to_Matrix()];d=int(d)*N
    if d<0:d=-d;vals=[-v for v in vals]
    g=gcd(d,*vals);d//=g;vals=[v//g for v in vals]
    G=np.array([vals[idx[orbit(x)]] for x in product(range(L),repeat=4)],dtype=object)
    assert sum(G)==0 and d%N==0
    assert np.array_equal(8*G-sum(shift(G,e)+shift(G,-e) for e in eye),np.array([d*(N*int(i==0)-1)//N for i in range(N)],dtype=object))
    print('PASS exact Green',m,'orbits',N,'point equations, denominator bits',d.bit_length(),flush=True)
    return G,d

def build():
    U=[link(sites,i)[:,:4,:] for i in range(4)];H={}
    def add(mu,nu,a,b,v):
        k=(mu,nu,tuple(b-a));w=shift(v,-a)
        if k in H:H[k]+=w
        else:H[k]=w.copy()
    def qproduct(fs):
        z=fs[0]
        for f in fs[1:]:z=mul(z,f)
        return z
    basis=np.zeros((3,4,4),dtype=np.int64)
    for i in range(3):basis[i,0,i+1]=1
    for mu in range(4):
        for nu in range(mu+1,4):
            dirs=[mu,nu,mu,nu];loc=[eye[0]*0,eye[mu],eye[nu],eye[0]*0]
            fs=[U[mu],shift(U[nu],eye[mu]),conj(shift(U[mu],eye[nu])),conj(U[nu])]
            first=[[mul(basis[c],f) if i<2 else -mul(f,basis[c]) for c in range(3)] for i,f in enumerate(fs)]
            tr=qproduct(fs)[...,0];diag=tr[...,None,None]*E
            for i in range(4):
                add(dirs[i],dirs[i],loc[i],loc[i],diag)
                for j in range(i+1,4):
                    block=np.empty((N,4,3,3),dtype=np.int64)
                    for c in range(3):
                        for e in range(3):
                            factors=fs.copy();factors[i]=first[i][c];factors[j]=first[j][e]
                            block[...,c,e]=-qproduct(factors)[...,0]
                    add(dirs[i],dirs[j],loc[i],loc[j],block)
                    add(dirs[j],dirs[i],loc[j],loc[i],block.swapaxes(-1,-2))
            print('Wilson plane',mu,nu,flush=True)
    ident=np.zeros((1,4,3,3),dtype=np.int64);ident[:,0]=E
    incidence=[(i,np.zeros(4,dtype=int),np.broadcast_to(ident,(N,4,3,3))) for i in range(4)]
    incidence += [(i,-eye[i],-rot(conj(shift(U[i],-eye[i])))) for i in range(4)]
    for mu,a,A in incidence:
        for nu,b,B in incidence:add(mu,nu,a,b,mm(A.swapaxes(-1,-2),B))
    for (mu,nu,d),h in H.items():
        other=H[nu,mu,tuple(-t for t in d)]
        assert np.array_equal(h,shift(other,d).swapaxes(-1,-2))
        expected=8*E if mu==nu and d==zero else -E if mu==nu and sum(abs(t) for t in d)==1 else np.zeros((3,3),dtype=int)
        assert np.all(h[:,0]==expected),(mu,nu,d)
    print('PASS all Hessian jet transpose relations and flat Laplacian identity;',len(H),'stencil blocks',flush=True)
    return H

def qjets():
    offsets=np.array(list(product(range(-6,7),repeat=4)),dtype=np.int64)
    q=np.empty((4,12,N,12),dtype=np.int64)
    for i in range(4):
        A,_=calc(i,offsets)
        for k in range(4):q[k,3*i:3*i+3]=A[:,:,k].transpose(2,0,1,3).reshape(3,N,12)
        print('Q rows',i,flush=True)
    return q,DEN

def actual_trace(H,G,den):
    tad=0
    for (mu,nu,d),h in H.items():
        if mu!=nu:continue
        idx=np.ravel_multi_index(tuple(t%L for t in d),shape)
        tad+=int(G[idx])*sum(int(x) for x in np.trace(h[:,3],axis1=-2,axis2=-1))
    print('exact tr G A_st =',S.Rational(tad,den),flush=True)
    return tad

def bubble(H,G,den):
    # tr G As G At: from As(x,x+d), At(y,y+e), weight g(y+e-x)*g(x+d-y).
    g=np.array([int(v)/den for v in G]).reshape(shape);entries={}
    for (mu,nu,d),h in H.items():
        if np.any(h[:,1]) or np.any(h[:,2]):
            entries.setdefault((mu,nu),[]).append((d,fftn(h[:,1].reshape(shape+(3,3)),axes=axes),fftn(h[:,2].reshape(shape+(3,3)),axes=axes)))
    cache={};res=0.
    for (mu,nu),ls in entries.items():
        for d,fs,_ in ls:
            for e,_,ft in entries.get((nu,mu),[]):
                key=(d,e)
                if key not in cache:
                    k=np.roll(g,tuple(-x for x in e),axis=axes)*np.roll(g,d,axis=axes);cache[key]=fftn(k)
                corr=(fs.conj()*ft.swapaxes(-1,-2)).sum(axis=(-1,-2))
                res+=float(np.vdot(cache[key],corr).real/N)
    return res

def lowrank(H,G,den,q,qd):
    # K0^-1 = [[G,L0],[L0^T,0]], L0 maps multipliers to constant fields.
    V=np.zeros((2,N,12,12),dtype=np.int64)
    for (mu,nu,d),h in H.items():
        for k in range(2):V[k,:,3*mu:3*mu+3,3*nu:3*nu+3]+=h[:,k+1]
    qsum=[S.Matrix([[sum(int(x) for x in q[k,i,:,j]) for j in range(12)] for i in range(12)])/qd for k in range(4)]
    assert qsum[0]==S.eye(12)
    exact=2*S.trace(qsum[3]-qsum[1]*qsum[2])
    ks=np.arange(L);lam=sum(2-2*np.cos(2*np.pi*ks.reshape(tuple(L if j==i else 1 for j in range(4)))/L) for i in range(4));lam[zero]=1
    cross=0.
    for k in range(2):
        v=V[k].reshape(shape+(12,12)).astype(float);f=fftn(v,axes=axes);f[zero]=0
        T=ifftn(f/lam[...,None,None],axes=axes).real.reshape(N,12,12)
        err=np.max(np.abs(8*T-sum(shift(T,e)+shift(T,-e) for e in eye)-(V[k]-V[k].mean(axis=0))))
        assert err<1e-9,err
        value=np.einsum('inj,nji->',q[2-k].astype(float)/qd,T,optimize=True)
        print('constraint cross',k,value,'Green residual',err,flush=True);cross+=value
    print('exact Q-only border contribution',exact,flush=True)
    return float(exact)-2*cross

if __name__=='__main__':
    G,d=green();H=build();tad=actual_trace(H,G,d);b=bubble(H,G,d);print('numerical full Wilson+gauge bubble=',b,flush=True)
    q,qd=qjets();cor=lowrank(H,G,d,q,qd)
    print('moving constraint correction=',cor,flush=True)
    print('finite 2 Gamma_st delta=',tad/d-b+cor,flush=True)
