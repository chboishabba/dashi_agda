"""Finite periodic full-exterior homogeneous correction and signed energy."""
import sympy as s
import numpy as np
from itertools import combinations

def run(X,G,H,J,F,A,B,R):
    S=G*A[3]; j=-s.Rational(6,5); c=-3*j
    assert S==S.T and S*J==3*R.T*H
    assert F.T*G*F==G and F*A[3]==-A[3]*F and R*F==-R
    assert H*B==B.T*H
    P=list(combinations(range(5),2)); pack=G.inv()*X.T
    pol=[s.diag(1,1,0),s.diag(1,0,1)]+[s.eye(3)[:,a]*s.eye(3)[:,b].T+s.eye(3)[:,b]*s.eye(3)[:,a].T for a,b in combinations(range(3),2)]
    arr=lambda x:np.asarray(x.tolist(),dtype=complex)
    g,h,ss,jj,ff,bb,rr,pk=map(arr,(G,H,S,J,F,B,R,pack))
    L=2*np.log(2); rng=np.random.default_rng(369); worst=0.; worstbc=0.; cases=0
    for sig in (-1,1):
        for gamma in (0.5,2.):
            for k in (2.,100.,10000.):
                tau=gamma+sig*1j*k; lam=np.sqrt(tau*tau+k*k); t=tau/k; l=lam/k
                xi=np.array([t,1j,0,0,-l]); vs=[np.array([l,0,0,0,-t]),np.eye(5)[2],np.eye(5)[3]]
                U=np.array([[xi[a]*v[b]-xi[b]*v[a] for v in vs] for a,b in P])
                Z=np.column_stack([(U@arr(p)@U.T).reshape(-1) for p in pol]); N=pk@Z; FN=ff@N
                assert np.linalg.norm(arr(X)@N-Z)<1e-10
                assert np.linalg.norm((t*np.eye(35)-1j*arr(A[0])+l*arr(A[3]))@N)<1e-10
                z=np.exp(-lam*L); wall=tau*np.eye(9)-1j*k*bb
                T=np.block([[(1-z)*(N-FN),(1-z)*(N+FN),-float(j)*jj],[np.zeros((9,5)),(1+z)*rr@N,wall]])
                v=rng.normal(size=19)+1j*rng.normal(size=19); f=T@v
                got,_,rank,_=np.linalg.lstsq(T,f,rcond=None); assert rank==19
                bc=np.linalg.norm(T@got-f)/max(1,np.linalg.norm(f)); assert bc<1e-9 and np.linalg.norm(got-v)<1e-6
                aa,ab,mm=got[:5],got[5:10],got[10:]; p=N@(aa+ab); q=FN@(aa-ab)
                wp=p+z*q; wm=z*p+q; mean=(wp+wm)/2
                assert np.linalg.norm(np.r_[wp-wm-float(j)*jj@mm,wall@mm+rr@mean]-f)<1e-6
                r=lam.real; b=lam.imag; I0=-np.expm1(-2*r*L)/(2*r); I1=np.exp(-r*L)*np.sin(b*L)/b
                energy=I0*(np.vdot(p,g@p)+np.vdot(q,g@q)).real+2*I1*np.vdot(p,g@q).real+float(c)*np.vdot(mm,h@mm).real
                work=-np.vdot(mean,ss@f[:35]).real+float(c)*np.vdot(mm,h@f[35:]).real
                err=abs(gamma*energy-work)/max(1,abs(work),gamma*energy); assert err<1e-7
                worst=max(worst,err); worstbc=max(worstbc,bc); cases+=1
    print('PASS',cases,'finite physical mode solves; max energy residual',worst,'max boundary residual',worstbc,flush=True)

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier,P,Q
    _,V,X,G,Y,H,J,A,B,R,_,_=carrier()
    F=V.gauss_jordan_solve(s.diag(*[(-1)**(int(4 in P[a])+int(4 in P[b])) for a,b in Q])*V)[0]
    run(X,G,H,J,F,A,B[0],R)
