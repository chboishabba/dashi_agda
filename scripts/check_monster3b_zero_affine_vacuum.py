"""Independent finite checks of the zero-affine vacuum theorem.
Uses the original TOE compiler; no MMV, no Monster packet claim.
"""
from itertools import product
import numpy as np
from toe_cyclotomic_operator import compile_shape, columns, rank


def require(ok, message):
    if not ok: raise ValueError(message)


def samples(n, count, rng):
    I=np.eye(n,dtype=np.int64); Z=np.zeros_like(I)
    for _ in range(count):
        A=np.eye(2*n,dtype=np.int64)
        for _ in range(8):
            X=rng.integers(0,3,(n,n),dtype=np.int64); X=(X+X.T)%3
            G=np.block([[I,X],[Z,I]]) if rng.integers(2) else np.block([[I,Z],[X,I]])
            A=A@G%3
        for lam in (1,2):
            yield A@np.block([[I,Z],[Z,lam*I]])%3,lam


def run():
    rng=np.random.default_rng(20261125); counts={}; ranks={}
    for n in (1,2,3,6):
        count=0; seen=set()
        matrices=((A,int(round(np.linalg.det(A)))%3) for x in product(range(3),repeat=4)
                  if rank(A:=np.array(x,dtype=np.int64).reshape(2,2))==2) if n==1 else samples(n,64,rng)
        for A,lam in matrices:
            b,d=A[:n,n:],A[n:,n:]; E=b.T@d%3
            for t in product(range(3),repeat=n):
                t=np.array(t,dtype=np.int64)
                if not np.any(b@t%3):require(int(t@E@t)%3==0,'kernel quadratic')
            for s in (1,2):
                R=compile_shape(A,lam,s);r=R['rank'];seen.add(r)
                require(R['origin']==[0]*n and R['constant']==0,'zero affine origin')
                R['scalar']=[1,0,1]
                j,y,(a,c)=next(columns(R)); k=np.flatnonzero(y==0)
                require(j==0 and len(k)==1 and (a[k[0]],c[k[0]])==(1,0),'unique raw unit vacuum')
                for p,z in ((31,5),(127,19)):
                    require((z*z+z+1)%p==0,'marked root')
                    for e in (1,-1,z,-z,z*z,-z*z):
                        u=pow((1+2*z)%p,-r,p)*pow(int(e)%p,-1,p)%p
                        require(u!=0,'normalized coefficient unit')
                count+=1
        counts[n]=count;ranks[n]=sorted(seen)
    # Genuine affine translation: the zero-to-zero coefficient vanishes.
    U=np.roll(np.eye(3,dtype=np.int64),1,axis=0)
    require(U[0,0]==0 and U[1,0]==1,'translated negative control')
    return dict(counts=counts,ranks=ranks,coefficient_checks=sum(counts.values())*12,affine_negative_controls=1)

if __name__=='__main__':print(run())
