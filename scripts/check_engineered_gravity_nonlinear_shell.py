"""Same-action smooth massive axisymmetric shell; finite Galerkin, not GR.
Original reciprocal action G(X) and dynamic order field, massless exterior DtN.
"""
import numpy as np
from scipy.sparse import coo_matrix, diags, bmat
from scipy.sparse.linalg import spsolve
from numpy.polynomial.legendre import leggauss, Legendre

def run(n,L,drive):
    a,b=.5,1.; r=np.linspace(a,b,n+1); dr=(b-a)/n; qx,qw=leggauss(5); mu,mw=leggauss(2*L+7)
    modes=np.arange(L+1); P=np.array([Legendre.basis(l)(mu) for l in modes]).T; DP=np.array([Legendre.basis(l).deriv()(mu) for l in modes]).T
    rr=[]; mm=[]; ww=[]; rows=[]; cols=[]; vals=[[],[],[]]; j=0
    for i in range(n):
      for t,w in zip(qx,qw):
       R=r[i]+dr*(1+t)/2
       for k,m in enumerate(mu):
        rr.append(R);mm.append(m);ww.append(w*dr/2*mw[k])
        for side in (0,1):
         shape=(1+t*(2*side-1))/2
         for l in modes:
          rows.append(j);cols.append((i+side)*(L+1)+l);vals[0].append(shape*P[k,l]);vals[1].append((2*side-1)/dr*P[k,l]);vals[2].append(shape*DP[k,l])
        j+=1
    N=(n+1)*(L+1); B,R,U=[coo_matrix((v,(rows,cols)),shape=(j,N)).tocsr() for v in vals]; rr=np.array(rr); mm=np.array(mm); w=np.array(ww)
    wr=w*rr**2; wu=w*(1-mm**2); X0=6*16*((rr-a)*(b-rr)/(b-a)**2)**2
    # X=X0+chi, chi zero at both anchors; controller source fixes X0 at drive=0.
    idx=np.arange(L+1,N-L-1); C=B[:,idx]; CR=R[:,idx]; CU=U[:,idx]
    def gram(A,w,D):return A.T@diags(w)@D
    def grad(c):return gram(R,wr*c,R)+gram(U,wu*c,U)
    def mass(c):return gram(B,wr*c,B)
    D=np.zeros(N); norm=2/(2*modes+1);D[:L+1]=a*modes*norm;D[-L-1:]=b*(modes+1)*norm
    Dt=diags(D); f=np.zeros(N);f[n*(L+1)+1]=3*b*b*drive*norm[1]
    # Positive massive shell fields; order perturbation stiffness and mass.
    base=grad(np.ones(j))+Dt+mass(np.ones(j)*.3); HX=gram(CR,wr,CR)+gram(CU,wu,CU)+gram(C,wr*2,C)
    chi=np.zeros(len(idx)); old=None
    for it in range(100):
      X=X0+C@chi; cross=-grad(X); Zmat=base+grad(X*X)
      q=spsolve(bmat([[base,cross],[cross,Zmat]],format='csc'),np.r_[f,np.zeros(N)]); p,z=q[:N],q[N:]
      pr,zr=R@p,R@z; pu,zu=U@p,U@z
      zz=wr*zr*zr+wu*zu*zu; pz=wr*pr*zr+wu*pu*zu
      new=spsolve((HX+gram(C,zz,C)).tocsc(),C.T@(pz-X0*zz))
      err=np.max(abs(new-chi));chi=new
      if err<1e-11:break
    X=X0+C@chi; res=np.r_[base@p-grad(X)@z-f, -grad(X)@p+(base+grad(X*X))@z, HX@chi+C.T@(X*zz-pz)]
    assert np.max(abs(res))<1e-8 and it<99
    assert np.max(abs(chi))<.2
    gain=p[1]/(a*drive); leak=z[1]/(a*drive)
    print(n,L,drive,'iterations',it+1,'residual',np.max(abs(res)),'gain',gain,'reference',leak,'order perturbation',np.max(abs(chi)),flush=True)
    return gain,leak
if __name__=='__main__':
    for n,L in ((12,3),(24,5),(48,7)):
      for e in (.1,.2):run(n,L,e)
