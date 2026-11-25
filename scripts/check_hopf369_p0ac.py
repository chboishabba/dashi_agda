"""P0AC: exact energy-coordinate exterior memory and nested-domain residual bound.
Original curved P0AA collar; flat expanding-domain control, not radiation solver.
"""
import numpy as np
from scipy.linalg import cholesky, solve_triangular, qr, block_diag, solve
from scipy.sparse.linalg import factorized
from itertools import product
import hopf369_exterior as aa
import check_hopf369_p0ab as ab

def memory():
    geom=aa.assemble(order=3); M,N=geom[:2]
    W=block_diag(cholesky(M),cholesky(N)); n=len(W); ne=len(M)
    # X=W(e,b); A is the exact energy-skew generator in these coordinates.
    L=solve_triangular(W[:ne,:ne].T,aa.C.T@W[ne:,ne:].T,lower=True)
    A=np.block([[np.zeros_like(M),L],[-L.T,np.zeros_like(N)]])
    ix=np.r_[aa.ie,ne+aa.iff]; R=np.eye(n)[ix]
    O=solve_triangular(W.T,R.T,lower=True).T
    U,_=qr(O.T,mode='full'); m=len(ix); Uc=U[:,:m]; Ur=U[:,m:]
    H=O@Uc; assert np.max(abs(O@Ur))<1e-12
    S=solve(H.T,Uc.T).T # energy-coordinate right inverse of O
    assert np.max(abs(O@S-np.eye(m)))<1e-12
    # Preserve actual observation and orthogonal residual, not the AB interpolation section.
    B=Uc.T@A@Ur; D=Ur.T@A@Ur; Ac=Uc.T@A@Uc
    assert np.max(abs(D+D.T))<1e-12
    dt=.12; E=np.eye(n); T=solve(E-dt*A/2,E+dt*A/2)
    assert np.max(abs(T.T@T-E))<1e-12
    Tq=U.T@T@U; a,b,c,d=Tq[:m,:m],Tq[:m,m:],Tq[m:,:m],Tq[m:,m:]
    # Nested exact frequency-domain elimination: full receiver then shared interface.
    # Receiver observed coordinates first, exterior energy residual second.
    sel=np.r_[np.isin(aa.ie,geom[7]),np.isin(aa.iff,geom[8])]
    # H rotates the actual observation basis; transform to physical receiver trace first.
    X=block_diag(H,np.eye(n-m)); Xi=block_diag(np.linalg.inv(H),np.eye(n-m))
    Z=X@(2.0*np.eye(n)-Tq)@Xi
    i=np.flatnonzero(sel); j=np.flatnonzero(~sel); k=np.arange(m,n)
    def schur(A,keep,omit):return A[np.ix_(keep,keep)]-A[np.ix_(keep,omit)]@solve(A[np.ix_(omit,omit)],A[np.ix_(omit,keep)])
    nested=schur(schur(Z,np.arange(m),k),i,j); direct=schur(Z,i,np.r_[j,k]); nested_error=np.max(abs(nested-direct));assert nested_error<1e-11
    # Continuous impedance K(s)=B(sI-D)^-1 B^T, positive real.
    pos=[]
    for s in (.1+.3j,.5+2j,2+5j):
        K=B@solve(s*np.eye(n-m)-D,B.T)
        pos.append(float(np.linalg.eigvalsh((K+K.conj().T)/2)[0]));assert pos[-1]>-1e-10
    # Same initial interior zero, exterior-only curl pulse. Retain complete residual.
    e=np.zeros(ne); p=e.copy();p[aa.ei[1,(2,-1,0)]]=.5;b0=aa.C@p
    X0=W@np.r_[e,b0]; assert np.max(abs(O@X0))<1e-12
    y0=Ur.T@X0; x0=Uc.T@X0; hist=[x0]; full=X0.copy(); r=y0.copy(); err=energy=0.
    # Actual same-current forcing enters both blocks; independent specified test currents.
    load=np.r_[-solve_triangular(W[:ne,:ne].T,aa.J,lower=True),np.zeros((len(N),108))]
    F=solve(E-dt*A/2,dt*load); Fq=U.T@F; f,g=Fq[:m],Fq[m:]
    inputs=[]; forcing_work=0.
    for t in range(16):
        current=.01*np.sin(np.arange(108)+t);inputs.append(current)
        # Explicit convolution from original initial complement and input history.
        rmem=np.linalg.matrix_power(d,t)@y0
        for j0 in range(t):rmem+=np.linalg.matrix_power(d,t-1-j0)@(c@hist[j0]+g@inputs[j0])
        assert np.max(abs(rmem-r))<1e-11
        xn=a@hist[-1]+b@rmem+f@current;rn=c@hist[-1]+d@rmem+g@current
        nxt=T@full+F@current; reconstructed=Uc@xn+Ur@rn
        err=max(err,np.max(abs(nxt-reconstructed)));forcing_work+=dt*((full+nxt)/2)@load@current
        energy=max(energy,abs((nxt@nxt-X0@X0)/2-forcing_work));hist.append(xn);r=rn;full=nxt
    assert err<1e-11 and energy<1e-10
    print('curved memory steps',len(inputs),'observation',m,'complement',n-m,'reconstruction',err,'energy closure',energy,'nested Schur',nested_error,'positive real minima',pos,'final observation norm',np.linalg.norm(O@full))

def domain(n):
    grid=ab.complex_grid(n);C=grid[2][1].astype(float);M=ab.flat_mass(n,1,n);N=ab.flat_mass(n,2,n);dt=.1
    E=factorized((2*M+dt**2/2*C.T@N@C).tocsc());p=np.zeros(M.shape[0]);p[grid[1][1][((1,),(n//2,n//2,n//2))]]=1
    return grid,C,M,N,E,(np.zeros(M.shape[0]),C@p)

def domains():
    # Unit spacing, same central compact curl pulse; compare nested reflecting boxes.
    large=domain(10); grid,C,M,N,E,state=large
    def advance(data,x):
        _,c,m,n,fac,_=data;e,b=x;v=fac(2*m@e+.1*c.T@n@b);return 2*v-e,b-.1*c@v
    reference=[state]
    for _ in range(12):reference.append(advance(large,reference[-1]))
    for width in (4,6,8):
        small=domain(width);offset=(10-width)//2
        maps=[np.array([grid[1][k][axes,tuple(x+offset for x in p)] for axes,p in small[0][0][k]]) for k in (1,2)]
        def embed(x):
            y=np.zeros(M.shape[0]);z=np.zeros(N.shape[0]);y[maps[0]]=x[0];z[maps[1]]=x[1];return y,z
        x=small[-1];bound=0.;errors=[];bounds=[];residual=[]
        assert all(np.array_equal(a,b) for a,b in zip(embed(x),state))
        # Unit-grid tensor-product mass lower bounds: M1>=1/36, N2>=1/6.
        # For larger (or infinite) flat grid each added cell contributes PSD mass.
        for t in range(12):
            xn=advance(small,x);yn=reference[t+1];e0,b0=embed(x);e1,b1=embed(xn)
            r=M@(e1-e0)-.1*C.T@N@((b1+b0)/2);s=b1-b0+.1*C@((e1+e0)/2)
            inc=np.sqrt(36*(r@r)+s@N@s);bound+=inc
            de,db=yn[0]-e1,yn[1]-b1;err=np.sqrt(de@M@de+db@N@db)
            assert err<=bound+1e-10;errors.append(err);bounds.append(bound);residual.append(inc);x=xn
        print('nested flat width',width,'steps',len(errors),'last error',errors[-1],'algebraic upper bound',bounds[-1],'max residual increment',max(residual))

if __name__=='__main__':memory();domains()
