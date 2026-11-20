"""Actual flat CMP98 Eq120 block-and-segment average on arbitrary 13m torus.
Wilson/Balaban source formula; new exact stencil, pivot, Gram and coercivity
reductions. Flat/reference results only, not the interacting beta or mass gap.
"""
from collections import Counter
from fractions import Fraction as F
import sympy as S
import numpy as np
from itertools import product
L=13; N=L**4; den=L**5
# Along the coarse-bond axis, the offset and crossing both have L choices.
w=Counter(x+j for x in range(-6,7) for j in range(L))
assert sum(w.values())==L**2 and w[0]==7 and w[L]==6
assert sum(v for x,v in w.items() if -6<=x<=6)==7*L
assert sum(v for x,v in w.items() if 7<=x<=19)==6*L
# Transverse 3 coordinates are uniform, so Gram numerator is L^3 times
# scalar along-axis numerator. Non-overlap outside shifts -L,0,+L.
diag=sum(v*v for v in w.values())
off=sum(v*w.get(x-L,0) for x,v in w.items())
assert diag==113*L and off==28*L
assert all(sum(v*w.get(x-k*L,0) for x,v in w.items())==0 for k in [-3,-2,2,3])
print('exact 1D path counts',sorted(w.items()))
print('Gram coefficients diag/off/floor',F(diag,L**7),F(off,L**7),F(diag-2*off,L**7))
assert F(diag-2*off,L**7)==F(57,4826809)
# 1D circulant check, including wraps (m=1 and m=2).
for m in [1,2,3,4,5,7,13,32,64]:
    A=np.zeros((m,m*L),dtype=np.int64)
    E=np.zeros((m*L,m),dtype=np.int64)
    for i in range(m):
        for x,v in w.items():A[i,(i*L+x)%(m*L)]+=v
        for x in range(-6,7):E[(i*L+x)%(m*L),i]=1
    T=np.roll(np.eye(m,dtype=np.int64),1,axis=1)
    P=7*np.eye(m,dtype=np.int64)+6*T
    assert np.array_equal(A[:,::L],P)
    assert np.array_equal(A@E,L*P)
    assert np.array_equal(A@A.T,diag*np.eye(m,dtype=np.int64)+off*(T+T.T))
    # independent rational cyclic inverse via finite geometric series.
    if m<=13:
        Tq=S.Matrix(T.tolist());I=S.eye(m);a=F(6,7)
        inv=sum(((-a)**k*Tq**k for k in range(m)),S.zeros(m))/(7*(1-(-a)**m))
        assert S.Matrix(P.tolist())*inv==I
        assert max(sum(abs(inv[i,j]) for j in range(m)) for i in range(m))<=1
    print('PASS m=',m,'pivot / Gram / block extension',flush=True)
# Exact open-block Poincare coefficients: variance=(1/L)sum_{i<j}(v_i-v_j)^2.
coeff=[F(sum(j-i for i in range(k+1) for j in range(k+1,L)),L) for k in range(L-1)]
assert coeff==[F((k+1)*(L-k-1),2) for k in range(L-1)] and max(coeff)==21
# Segment average S, h-Sh = weighted sum of shifted first differences;
# ||h-Sh|| <= ((L-1)/2)||grad_mu h||. Norm squared sum weights = 36.
segment=sum(F(j,L) for j in range(L));assert segment==6
assert max(coeff)+segment**2==57
print('PASS volume-independent flat constraint coercivity 1/57, exact combinatorial coefficients')

# Numerical fiber inverse and alias normalization checks, separately from
# the exact order proof. Fine p=(coarse k + 2*pi*alias)/L. Unweighted
# Fourier isometries: q vector = product box Fourier factors * segment /sqrt(N).
# Use normalized coarse inner product (N times physical coarse sum), so
# sqrt(N) factor removed. At k=0 q=(1,0,...), Green invert on mean-zero.
def fibers(m):
    aliases=np.arange(L);coarse=2*np.pi*np.arange(m)/m
    min_gram=1.;min_floor=1.;max_err=0.
    rng=np.random.default_rng(123)
    for idx in product(range(m),repeat=4):
        p=[(coarse[k]+2*np.pi*aliases)/L for k in idx]
        box=[np.exp(1j*np.outer(u,np.arange(-6,7))).mean(axis=1) for u in p]
        seg=[np.exp(1j*np.outer(u,np.arange(L))).mean(axis=1) for u in p]
        def lift(a,i):return a.reshape(tuple(L if k==i else 1 for k in range(4)))
        boxprod=np.prod(np.broadcast_arrays(*[lift(box[i],i) for i in range(4)]),axis=0)
        lam=sum(lift(2-2*np.cos(p[i]),i) for i in range(4)).reshape(-1)
        for mu in range(4):
            q=(boxprod*lift(seg[mu],mu)).reshape(-1)
            gram=np.vdot(q,q).real
            # normalized Gram symbol 113/169 + 56/169 cos(k_mu).
            expect=(113+56*np.cos(coarse[idx[mu]]))/169
            assert abs(gram-expect)<1e-12
            min_gram=min(min_gram,gram)
            # Check coercivity witness A0 + alpha Q*Q >= c I with c<1/57.
            # diagonal minus c has at most one negative (alias low mode); Schur
            # complement makes exact positivity criterion for rank-one update.
            c=1/57
            small=lam<c
            assert small.sum()<=1
            if small.any():
                # restriction ker q, eliminate low mode; positivity iff
                # lam0-c + 1/(sum |qi/q0|²/(lami-c)) >= 0.
                q0=q[small][0];gap=lam[small][0]-c
                z=np.sum(np.abs(q[~small]/q0)**2/(lam[~small]-c))
                margin=gap+1/z if z>0 else np.inf
                assert margin>0
            # Test bordered inverse on arbitrary RHS, with a special zero mode.
            x=rng.normal(size=N)+1j*rng.normal(size=N);r=0.13-0.21j
            if all(k==0 for k in idx):
                y=x.copy();y[0]=0;y[1:]/=lam[1:];y[0]=r/q[0];z=x[0]/q[0].conjugate()
            else:
                g=1/lam;z=(q@(g*x)-r)/(q@(g*q.conj()));y=g*(x-q.conj()*z)
            err=max(np.max(np.abs(lam*y+q.conj()*z-x)),abs(q@y-r))
            assert err<2e-10,err;max_err=max(max_err,err)
    print('PASS fiber m=',m,'coarse momenta',m**4,'Gram min',min_gram,'border residual',max_err,flush=True)
if __name__=='__main__':
    for m in [1,2,3]:fibers(m)
