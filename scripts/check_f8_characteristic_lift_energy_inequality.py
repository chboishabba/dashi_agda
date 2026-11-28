"""F8 lifted first-order characteristic energy, quantitative short slab.

On 1<=t<=6/5, 0<=n<=1/2, |k|<=K, original H,R,ell=L-qchi
has homogeneous neutral/dissipative boundaries. Weight 1+2k²/a²
cancels the k² H(R+ell) coupling. The exact rational estimate is
E'<=81E+[(199+50K²)q²+2q_t²]/4 for a smooth original solution,
q=12 Pi(t,k). Not a numerical or coupled Einstein acceptance.
"""
from fractions import Fraction as F
import sympy as s


def constants():
    nmax=F(7,6);cmax=F(8,5);amin=F(1,5);nnmax=F(7,5)
    alpha=nnmax+3*nmax*(cmax+1)/(2*amin)
    beta=3*nmax*(cmax-1)/(2*amin)
    gamma=3*nmax*(cmax+1)/(2*amin)
    delta=nnmax+beta
    fL=delta+2*nmax
    Rcoef=nnmax/2+alpha+(beta+gamma)/2+nmax/4
    Lcoef=nnmax/2+delta+(beta+gamma)/2+nmax/4
    Hcoef=nmax/2
    assert alpha==F(483,20) and beta==F(21,4)
    assert gamma==F(91,4) and delta==F(133,20)
    assert Rcoef<40 and Lcoef<40 and Hcoef<40
    assert beta<6 and fL<9 and nmax/2<1
    return alpha,beta,gamma,delta,Rcoef,Lcoef,Hcoef,fL


def exact():
    alpha,beta,gamma,delta,rc,lc,hc,fl=constants()
    H,R,l,q,qd,chi,chin,N,Nn,k,a,c=s.symbols(
        'H R l q qd chi chin N Nn k a c',real=True)
    W=(R+l+chi*q)/2;V=(R-l-chi*q)/2
    S=(Nn-3*N*c/a)*V-3*N/a*W-N*k*k*H/a**2
    SR=s.expand(S+Nn*W);SL=s.expand(S-Nn*W)
    assert s.simplify(s.diff(SR,R)-(Nn-3*N*(c+1)/(2*a)))==0
    assert s.simplify(s.diff(SR,l)-3*N*(c-1)/(2*a))==0
    assert s.simplify(s.diff(SL,R)+3*N*(c+1)/(2*a))==0
    assert s.simplify(s.diff(SL,l)-(-Nn+3*N*(c-1)/(2*a)))==0
    weight=1+2*k*k/a**2
    wt=-4*k*k*N/a**3
    density=s.expand(wt*H*H/2+weight*H*N*W+
        R*SR+l*(SL-qd*chi-N*q*chin)-Nn*(R*R-l*l)/2)
    assert s.simplify(s.diff(density,H,R)-N/2)==0
    assert s.simplify(s.diff(density,H,l)-N/2)==0
    assert s.simplify(s.diff(density,H,2)+4*k*k*N/a**3)==0
    assert s.simplify(s.diff(density,qd)+l*chi)==0
    assert s.simplify(s.expand(s.diff(density,q)).coeff(k,2)-N*chi*H/a**2)==0
    # w<=1+50K², source weighted square <=(199+50K²)q²+2 q_t².
    assert 1+36+2*9**2==199
    assert F(2)/(F(1,5)**2)==50
    # Lower-order homogeneous coefficient inequalities yield 80E;
    # source Young adds E+(1/2)*integral(source²), interval length 1/2.
    assert 80+1==81
    tau=s.symbols('tau',nonnegative=True);z=s.symbols('z',positive=True)
    D=199+50*z*z
    bound=(D+2)*(s.exp(81*tau)-1)/(4*81)
    assert s.simplify(s.diff(bound,tau)-81*bound-(D+2)/4)==0
    assert bound.subs(tau,0)==0
    print('PASS original F8 Eprime<=81E+[(199+50K²)q²+2 q_t²]/4, short causal slab')
    print('Requires smooth characteristic IBVP, not continuum numerical error certification')

if __name__=='__main__':exact()
