"""Original F8 seven-level lifted characteristic constructor.

Conditional on smooth original IBVP on [1,6/5], not a continuum existence
or receiver certificate. Exact rational coefficient majorants, no CI.
"""
from fractions import Fraction as F
from math import comb
import sympy as s

ORDER=6

def close(N,M,f):
    """Actual derivative jets (not Taylor coefficients); return B,b.
    C_r=U_(r+1)-sum binom(r,j) M_j U_(r-j)-f_r.
    The recursion eliminates A d_n U_r without inverting singular A.
    """
    p=len(N)-1
    if N[0]==0 or len(M)!=p+1 or len(f)!=p+1:
        raise ValueError("nonzero lapse and matching jets required")
    I=s.eye(3); Z=s.zeros(3); z=s.zeros(3,1)
    B=[]; b=[]; V=[]; v=[]
    for m in range(p+1):
        row=[comb(m,r)*M[m-r] for r in range(m+1)]
        src=f[m]
        for j in range(1,m+1):
            for r in range(m-j+2):
                row[r]=row[r]+comb(m,j)*N[j]*V[m-j][r]
            src=src+comb(m,j)*N[j]*v[m-j]
        B.append(row); b.append(src)
        if m<p:
            V.append([-x/N[0] for x in row]+[I/N[0]])
            v.append(-src/N[0])
    return B,b

def mul(x,y):
    return [sum(comb(m,j)*x[j]*y[m-j] for j in range(m+1))
            for m in range(len(x))]

def inv(x,lower):
    y=[1/F(lower)]
    for m in range(1,len(x)):
        y.append(sum(comb(m,j)*x[j]*y[m-j] for j in range(1,m+1))/lower)
    return y

def caps(K):
    """Absolute derivative caps from a'=c/g,c'=a/g,g^2=1+t^2.
    Uses original collar rational bounds; all operations positive."""
    K=F(K)
    if K<0: raise ValueError("nonnegative cutoff")
    p=ORDER
    g=[F(8,5),F(1)]
    for m in range(2,p+1):
        g.append((F(2) if m==2 else F(0))/F(14,5)
                 +sum(comb(m,j)*g[j]*g[m-j] for j in range(1,m))/F(14,5))
    ig=inv(g,F(7,5))
    a=[F(7,5)]; c=[F(8,5)]
    for m in range(p):
        a.append(mul(c,ig[:m+1])[m])
        c.append(mul(a[:m+1],ig[:m+1])[m])
    N=mul(c,ig); Nn=mul(a,ig)
    ia=inv(a,F(1,5))
    nc=mul(mul(N,c),ia); na=mul(N,ia)
    kterm=[K*K*x for x in mul(na,ia)]
    M=[]; A=[]
    for j in range(p+1):
        d=3*(nc[j]+na[j])/2
        M.append(s.Matrix([[0,N[j]/2,N[j]/2],
                  [kterm[j],Nn[j]+d,d],
                  [kterm[j],d,Nn[j]+d]]))
        A.append(s.Matrix([N[j]/2,d,Nn[j]+d+2*N[j]]))
    return N,M,A

def majorants(K,Q):
    """Q_j bounds |q_j| for j=0..7, actual prescribed q=12 Pi.
    Returns positive block/forcing caps and conditional energy/trace rates.
    """
    K=F(K); Q=list(map(F,Q))
    if len(Q)!=8 or min(Q)<0: raise ValueError("need nonnegative q0..q7 caps")
    N,M,A=caps(K); B=[]; b=[]; V=[]; v=[]
    for m in range(ORDER+1):
        row=[comb(m,r)*M[m-r] for r in range(m+1)]
        src=sum((comb(m,j)*A[j]*Q[m-j] for j in range(m+1)),s.zeros(3,1))
        src[2]+=Q[m+1]
        for j in range(1,m+1):
            for r in range(m-j+2):
                row[r]+=comb(m,j)*N[j]*V[m-j][r]
            src+=comb(m,j)*N[j]*v[m-j]
        B.append(row); b.append(src)
        if m<ORDER:
            V.append([x*F(5,3) for x in row]+[s.eye(3)*F(5,3)])
            v.append(src*F(5,3))
    # Weighted operator norm <= (1+50K^2) entrywise l1 norm.
    w=1+50*K*K
    rates=[[w*sum(x) for x in row] for row in B]
    gamma=s.zeros(7); forcing=s.zeros(7,1)
    for m in range(7):
        # G_t<=0; integration by parts adds <= |N_n| E_m;
        # use original |N_n|<7/5, plus source Young increment 1.
        gamma[m,m]=2*rates[m][m]+F(7,5)+1
        for r in range(m):
            gamma[m,r]=rates[m][r]
            gamma[m,m]+=rates[m][r]
        forcing[m]=w*sum(x*x for x in b[m])/4
    # Backward characteristics: ell reflects to R at n=0, R terminates
    # at outer zero boundary or initial slice; H is vertical. At most one
    # reflection; no multiplicative boundary gain. Sup-norm Gronwall.
    trace_rate=max(max(sum(sum(row[i,j] for j in range(3)) for row in rows)
                       for i in range(3)) for rows in B)
    trace_force=max(max(vec) for vec in b)
    return gamma,forcing,trace_rate,trace_force

def exact():
    # Independent polynomial manufactured field at a rational spacetime point.
    t,n=s.symbols("t n"); A=s.diag(0,1,-1)
    N=2+t+n+t*n
    M=s.Matrix([[0,t,1],[t*t,1,n],[1,t*n,t]])
    U=s.Matrix([t**7+n*t**3, t**6*n+n*n, t**8+n*t])
    f=U.diff(t)-N*A*U.diff(n)-M*U
    at=lambda x:x.subs({t:s.Rational(11,10),n:s.Rational(1,4)})
    jet=lambda x:[at(s.diff(x,t,j)) for j in range(7)]
    B,b=close(jet(N),jet(M),jet(f))
    for m in range(7):
        rhs=at(N)*A*at(U.diff(t,m).diff(n))+b[m]
        for r in range(m+1): rhs+=B[m][r]*at(U.diff(t,r))
        assert rhs==at(U.diff(t,m+1))
    from check_f8_original_pulse_derivative_bounds import fourier_source_bounds
    Q=[12*x for x in fourier_source_bounds(40,7)]
    G,Fv,L,J=majorants(40,Q)
    assert all(x>=0 for x in G) and all(x>=0 for x in Fv)
    assert all(G[i,j]==0 for i in range(7) for j in range(i+1,7))
    assert L>0 and J>0
    assert majorants(40,[0]*8)[1]==s.zeros(7,1)
    # Conditional uniform trace cap with flat initial state:
    # S(t)<=J*(exp(L*(t-1))-1)/L. Keep exponential symbolic.
    # H7 wall cap <= S sum binom(6,j) Ncap[j]
    # + 1/2 sum binom(6,j) Ncap[j] Q[6-j].
    print("PASS seven-level coefficient replay, original rational bounds and trace comparison construction")
    print("Conditional smooth short-slab only; no native or physical receiver acceptance")

if __name__=="__main__":
    exact()
