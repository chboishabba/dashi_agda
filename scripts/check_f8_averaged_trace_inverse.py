"""Actual strict-lower piecewise-constant kernel lift, not nodal collocation.
Conditional finite inverse and short-lag diagonal obstruction; no global delta upper.
"""
import json,sys,time,math
from fractions import Fraction as Q
import numpy as np
from scipy.linalg import solve_triangular
from check_f8_global_wall_kernel import clock,kernels

U=lambda x:np.nextafter(x,np.inf)
D=lambda x:np.nextafter(x,-np.inf)

def inverse(L):
    n=len(L);Id=np.eye(n);A=Id-L;G=solve_triangular(A,Id,lower=True);eps=2.**-53;gamma=U(2*n*eps/(1-2*n*eps))
    def norm(X):return U(U(np.max(np.sum(abs(X),axis=1))/D(1-gamma))+1e-290)
    P=A@G;E=Id-P;rho=U(2*(norm(E)+U(gamma*U(norm(A)*norm(G)))+U(eps*(1+norm(P)))+1e-290));assert rho<1
    # A^-1-I=G-I+(A^-1-G), latter <= ||G||rho/(1-rho).
    off=U(norm(G-Id)+U(eps*U(norm(G)+1)))
    corr=U(U(norm(G)*rho)/D(1-rho));lift=U(1+U(off+corr))
    return lift,rho,D(1/lift)

def diagonal_lower(dt,bmax):
    # Exact local kernel estimates via geometric majorant of Picard series.
    # Uniform V <= M, A B <= dt^2, A+B <= 2 dt. K=R/2.
    h=Q(dt);b=Q(bmax);M=Q(15*13**2,4)+9;x=M*h*h/4;assert x<Q(1,2)
    Klo=(1-x/(1-x))/2;d=M*h/(4*(1-x));Llo=3*Klo/b-2*(1+b)*d
    assert Llo>0
    return h*Llo

def diagonal_lift(L,dt,bl,bh,mode):
    # D_i f(t)=d_i integral_{left_i}^t f. Exact local resolvent R_i.
    # Q R_i J=phi_i, where phi_i=(exp(d_i h)-1)/(d_i h).
    # x=R f+R J L (I-Phi L)^-1 Q R f; no time-node interpretation.
    h=Q(dt);n=len(L);rates=3/(bl+bh);pl=[];ph=[];eu=[];diag=[]
    for d,b0,b1 in zip(rates,bl,bh):
        d=Q(float(d));b0=Q(float(b0));b1=Q(float(b1));x=d*h
        s=sum(x**j/math.factorial(j) for j in range(25));e=s+x**25/math.factorial(25)/(1-x/26)
        pl.append(D(float((s-1)/x)));ph.append(U(float((e-1)/x)));eu.append(U(float(e)))
        M=Q(9)+Q(15,4)/max(Q(1,13),b0-h/2)**2;y=M*h*h/4;assert y<1
        # On diagonal: lag derivative bound O(lag), K-1/2 O(lag²).
        err=(1+b1)*M*h*h/(4*(1-y))+M*h**3/(8*b0*(1-y))+h*max(abs(Q(3,2)/b0-d),abs(Q(3,2)/b1-d))
        diag.append(U(float(err)))
    pl,ph,eu=map(np.array,(pl,ph,eu));p=(pl+ph)/2;Id=np.eye(n);A=Id-p[:,None]*L;G=solve_triangular(A,Id,lower=True);eps=2.**-53;gamma=U(2*n*eps/(1-2*n*eps))
    def norm(X):return U(U(np.max(np.sum(abs(X),axis=1))/D(1-gamma))+1e-290)
    dp=U(np.max(np.maximum(U(p-pl),U(ph-p))));deltaA=U(U(dp+U(eps*ph.max()))*norm(L)+1e-290)
    P=A@G;E=Id-P;rho=U(2*(norm(E)+U(gamma*U(norm(A)*norm(G)))+U(eps*(1+norm(P)))+U(deltaA*norm(G))+1e-290));assert rho<1
    off=U(norm(G-Id)+U(eps*U(norm(G)+1)));corr=U(U(norm(G)*rho)/D(1-rho));lift=U(eu.max()*U(1+U(U(ph.max()/pl.min())*U(off+corr))))
    threshold=D(1/lift);dmax=max(diag)
    return dict(diagonal_exact_lift_inverse_upper=float(lift),diagonal_exact_inverse_defect=float(rho),required_delta_below=float(threshold),diagonal_error_upper=float(dmax),remaining_offdiagonal_budget=float(D(threshold-dmax)),scope='diagonal block retained analytically; offdiagonal whole-cell kernel enclosure unpaid')

def run(n):
    start=time.monotonic();dt,t,b,lo,hi,span=clock(n);h=1/(2*min(n,256));rows=[];dl=diagonal_lower(dt,hi[1])
    for mode in (1,2):
        K,Kt,Kx,_=kernels(t,b,lo,hi,dt,h,mode,False);bF=b[::-1];v=-bF/np.sqrt(1+bF*bF);K=K[::-1,::-1];Kt=Kt[::-1,::-1];Kx=Kx[::-1,::-1]
        # On I_i x I_j, j<i, choose constant Khat equal to sampled right endpoints.
        # Q averages each cell, J embeds constants. Vhat=J L Q, diagonal omitted.
        L=np.tril(2*(Kx[1:,1:]-Kt[1:,1:]*v[None,1:]+1.5*K[1:,1:]/bF[None,1:])*dt,-1)
        lift,rho,threshold=inverse(L);rows.append(dict(mode=mode,finite_lift_inverse_upper=float(lift),inverse_defect=float(rho),required_delta_below=float(threshold),diagonal_delta_lower=float(D(float(dl))),strict_lower_perturbation_gate_impossible_for_this_bound=bool(Q(threshold)<dl),diagonal_retained=diagonal_lift(L,dt,lo[::-1][1:],hi[::-1][:-1],mode)))
    return dict(n=n,seconds=time.monotonic()-start,rows=rows,scope='literal finite-rank averaged operator on whole cells; IEEE conditional finite inverse, exact diagonal lower; no global delta upper or continuous inverse certificate')
if __name__=='__main__':print(json.dumps(run(int(sys.argv[1])),indent=2),flush=True)
