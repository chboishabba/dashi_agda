"""Finite compliance extension of the original reciprocal shell.
X=B0+bias+chi; X-B=chi, B=B0+bias. Both order and bias vary.
B0 is a prescribed rest profile: its reaction is retained, not removed.
No continuum, physical material or Einstein acceptance.
"""
import numpy as np
from scipy.sparse import coo_matrix, diags, bmat
from scipy.sparse.linalg import spsolve
from numpy.polynomial.legendre import leggauss, Legendre
from numpy.polynomial import Polynomial
from scipy.signal import convolve2d
from math import comb

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
    # Support stiffness 4 and mass squared 8; a chosen effective compliance.
    HB=4*HX
    chi=np.zeros(len(idx)); bias=np.zeros_like(chi)
    for it in range(100):
      X=X0+C@(chi+bias); cross=-grad(X); Zmat=base+grad(X*X)
      q=spsolve(bmat([[base,cross],[cross,Zmat]],format='csc'),np.r_[f,np.zeros(N)]); p,z=q[:N],q[N:]
      pr,zr=R@p,R@z; pu,zu=U@p,U@z
      zz=wr*zr*zr+wu*zu*zu; pz=wr*pr*zr+wu*pu*zu
      V=gram(C,zz,C); rhs=C.T@(pz-X0*zz)
      new=spsolve(bmat([[HX+V,V],[V,HB+V]],format='csc'),np.r_[rhs,rhs])
      newchi,newbias=np.split(new,2)
      err=max(np.max(abs(newchi-chi)),np.max(abs(newbias-bias)))
      chi,bias=newchi,newbias
      if err<1e-11:break
    X=X0+C@(chi+bias)
    g=C.T@(X*zz-pz)
    res=np.r_[base@p-grad(X)@z-f, -grad(X)@p+(base+grad(X*X))@z, HX@chi+g, HB@bias+g]
    # Variation holding X fixed: E_B = HB*bias-HX*chi.
    assert np.max(abs(HB@bias-HX@chi))<1e-8
    # External rest-profile reaction in the material coordinates remains g.
    # At the stationary branch this equals -HB*bias.
    assert np.max(abs(g+HB@bias))<1e-8
    # Cellwise polynomial Bernstein envelope, retaining cancellation in q.
    # Floating arithmetic (not outward-rounded interval certification).
    full=np.zeros(N);full[idx]=chi+bias
    leg=np.zeros((L+1,L+1))
    for l in modes:
        coeff=Legendre.basis(l).convert(kind=Polynomial)(Polynomial([-1,2])).coef
        leg[l,:len(coeff)]=coeff
    def pol(v,i):
        V=v.reshape(n+1,L+1)@leg
        return np.stack([V[i],V[i+1]-V[i]])
    def sub(A,B):
        S=np.zeros(tuple(max(x,y) for x,y in zip(A.shape,B.shape)))
        S[:A.shape[0],:A.shape[1]]+=A;S[:B.shape[0],:B.shape[1]]-=B
        return S
    def cap(A):
        m,n0=np.array(A.shape)-1
        T=lambda k:np.array([[comb(i,j)/comb(k,j) if j<=i else 0 for j in range(k+1)] for i in range(k+1)])
        return np.max(abs(T(m)@A@T(n0).T))
    qcap=0.
    for i in range(n):
        P0,Z0,X1=pol(p,i),pol(z,i),pol(full,i)
        rp=Polynomial([r[i],dr]); bg=96*((rp-a)*(b-rp)/(b-a)**2)**2
        X1=sub(X1,-bg.coef[:,None]); Rq=sub(P0[1:]/dr,convolve2d(X1,Z0[1:]/dr))
        dmu=lambda A:A[:,1:]*np.arange(1,A.shape[1])/2
        Uq=sub(dmu(P0),convolve2d(X1,dmu(Z0)))
        qcap=max(qcap,np.hypot(cap(Rq),cap(Uq)/r[i]))
    # Reserve half each mass, using 2 q^2 (dchi+db)^2 <= 4 q^2(dchi^2+db^2).
    margin=2-4*qcap*qcap
    assert margin>0
    # Actual quadrature value, distinct from the polynomial envelope.
    qsample=np.max(np.sqrt((pr-X*zr)**2+(1-mm*mm)/rr**2*(pu-X*zu)**2))
    print('q sample',qsample,'q cap',qcap,'sufficient margin',margin,'support reaction',np.max(abs(g)),flush=True)
    assert np.max(abs(res))<1e-8 and it<99
    assert np.max(abs(chi))<.2
    gain=p[1]/(a*drive); leak=z[1]/(a*drive)
    print(n,L,drive,'iterations',it+1,'residual',np.max(abs(res)),'gain',gain,'reference',leak,'order perturbation',np.max(abs(chi)),'bias perturbation',np.max(abs(bias)),flush=True)
    return gain,leak
if __name__=='__main__':
    for n,L in ((12,3),(24,3),(24,5),(48,5),(48,7)):
      for e in (.1,.2):run(n,L,e)
