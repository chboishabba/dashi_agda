"""Composed flat finite-collar energy; source-compatible manufactured audit."""
import numpy as np
import sympy as s
from numpy.polynomial.legendre import leggauss
from check_hopf369_br220_normal_constraint_propagation import symbols

def run(X,G,H,J,F,A,B,R):
    C,K=symbols(X,G); arr=lambda x:np.asarray(x.tolist(),complex)
    C=list(map(arr,C)); K=list(map(arr,K)); g,h,jj,ff,bb,rr=map(arr,(G,H,J,F,B,R)); aa=list(map(arr,A)); S=g@aa[3]; j=-1.2;c=-3*j
    I=np.eye(35); Q=np.eye(100)-C[4]@K[4]; L=2*np.log(2); rng=np.random.default_rng(369)
    rows=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,16,17,18,19,31,32,33,37,38,39]; cols=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,18,22,26,29,30,31,32,33,34]
    Z=I[:,[i for i in range(35) if i not in cols]]; E=I[:,cols]; H0=Z.T
    ghalf=np.linalg.cholesky(g).conj().T
    norm=lambda w:np.linalg.norm(ghalf@w)
    nodes,weights=leggauss(256); nodes=(nodes+1)*L/2; weights*=L/2
    worst=0.; worstbc=0.; maxratio=0.; count=0
    for sig in (-1,1):
      for gamma in (.5,2.):
       for k in (100.,1000.,10000.):
        tau=gamma+sig*1j*k; t=tau/k; lam=np.sqrt(tau*tau+k*k); r=lam.real; assert r*L>=3
        b=t*C[0]+1j*C[1]; D=Q@b; a=-K[4]@b; V=E@np.linalg.solve(D[np.ix_(rows,cols)],np.eye(100)[rows]); N=Z-V@D@Z; M=H0@a@N
        pp=(np.eye(10)+k*M/lam)/2; pm=np.eye(10)-pp
        w0=rng.normal(size=35)+1j*rng.normal(size=35); w1=rng.normal(size=35)+1j*rng.normal(size=35)
        # Manufactured affine source; stable particular lift recovered by endpoint subtraction.
        p0=N@pm@H0@w0; pL=N@pp@H0@(w0+L*w1)
        def part(y):return w0+y*w1-np.exp(-lam*y)*p0-np.exp(-lam*(L-y))*pL
        # physical homogeneous modes from regular reduced projector SVD
        um=np.linalg.svd(pm)[0][:,:5]; up=np.linalg.svd(pp)[0][:,:5]; Nm=N@um; Np=N@up; z=np.exp(-lam*L)
        jump=np.column_stack(((1-z)*Nm,-(1-z)*Np,-j*jj)); wall=tau*np.eye(9)-1j*k*bb
        T=np.vstack((jump,np.column_stack(((1+z)*rr@Nm/2,(1+z)*rr@Np/2,wall))))
        v=rng.normal(size=19)+1j*rng.normal(size=19); rhs=T@v
        v2,_,rank,_=np.linalg.lstsq(T,rhs,rcond=None); assert rank==19
        p=Nm@v2[:5]; q=Np@v2[5:10]; m=v2[10:];
        def field(y):return part(y)+np.exp(-lam*y)*p+np.exp(-lam*(L-y))*q
        wp,wm=field(0),field(L); mean=(wp+wm)/2; fj=wp-wm-j*jj@m; fw=wall@m+rr@mean
        target=rhs+np.r_[part(0)-part(L),rr@(part(0)+part(L))/2]
        bc=np.linalg.norm(np.r_[fj,fw]-target)/max(1,np.linalg.norm(target)); worstbc=max(worstbc,bc)
        d=lambda y:(tau*I-1j*k*aa[0])@(w0+y*w1)-aa[3]@w1
        bulk=sum(w*norm(field(y))**2 for y,w in zip(nodes,weights)); partnorm=np.sqrt(sum(w*norm(part(y))**2 for y,w in zip(nodes,weights))); hn=np.sqrt(sum(w*norm(field(y)-part(y))**2 for y,w in zip(nodes,weights)))
        energy=bulk+c*np.vdot(m,h@m).real; work=sum(w*np.vdot(field(y),g@d(y)).real for y,w in zip(nodes,weights))-np.vdot(mean,S@fj).real+c*np.vdot(m,h@fw).real
        err=abs(gamma*energy-work)/max(1,abs(work),gamma*energy); worst=max(worst,err)
        meanpart=(part(0)+part(L))/2; tracebound=3*np.sqrt(r)*hn+norm(meanpart)
        assert norm(mean)<=tracebound*(1+1e-10)
        jumpdual=np.linalg.norm(np.linalg.solve(ghalf.conj().T,S@fj)); dnorm=np.sqrt(sum(w*norm(d(y))**2 for y,w in zip(nodes,weights))); wallnorm=np.sqrt(c*np.vdot(fw,h@fw).real)
        A0=dnorm+wallnorm+3*np.sqrt(r)*jumpdual; B0=(3*np.sqrt(r)*partnorm+norm(meanpart))*jumpdual
        upper=A0/gamma+np.sqrt(B0/gamma); ratio=np.sqrt(energy)/upper; maxratio=max(maxratio,ratio); assert ratio<=1+1e-8
        count+=1
    assert worst<1e-8 and worstbc<1e-8
    print('PASS',count,'composed finite collar cases; energy residual',worst,'boundary residual',worstbc,'max bound ratio',maxratio)

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier,P,Q
    _,V,X,G,Y,H,J,A,B,R,_,_=carrier()
    F=V.gauss_jordan_solve(s.diag(*[(-1)**(int(4 in P[a])+int(4 in P[b])) for a,b in Q])*V)[0]
    run(X,G,H,J,F,A,B[0],R)
