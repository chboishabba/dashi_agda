"""Exact rational certificate for selected E:y^2=x^3-66x+289.
Classical inputs: Tate's algorithm, modularity/Fricke/Mellin, Hasse,
analytic-rank-zero theorem of Kolyvagin, prior independent MW rank certificate.
No floating point enters certificate comparisons.
"""
from fractions import Fraction as Q
from math import isqrt
import numpy as np
import sympy as sp

checks=0
def check(b):
    global checks
    if not b: raise AssertionError('exact check failed')
    checks+=1
A,B=-66,289
D=-16*(4*A**3+27*B**2); c4=-48*A
check(D==-17681328 and sp.factorint(-D)=={2:4,3:4,7:1,1949:1})
# Minimal everywhere since v(Delta)<12. Tate II at 3, III at 2.
check(288%4==0 and (-66**2)%8!=0 and all(v%2==0 for v in [2,-66,288]))
check(354%9!=0 and all(v%3==0 for v in [-3,-63,354]))
check(c4%7!=0 and c4%1949!=0)
N=2**3*3**4*7*1949; check(N==8840664)
bad={2:0,3:0}
for p in [7,1949]:
    roots=[x for x in range(p) if (x**3+A*x+B)%p==0 and (3*x*x+A)%p==0]
    check(len(roots)==1 and (3*roots[0])%p!=0)
    bad[p]=int(sp.legendre_symbol(3*roots[0]%p,p))
check(bad=={2:0,3:0,7:-1,1949:1})
M=20000
# Exact integer point counts, multiplicativity and local recurrence.
# int64 intermediates < 2^63: x^2,p^2<4e8, and coefficient products <=2M.
a=np.ones(M+1,dtype=np.int64);a[0]=0
for p in map(int,sp.primerange(2,M+1)):
    if p in bad: v=bad[p]
    else:
        x=np.arange(p,dtype=np.int64);sq=np.full(p,-1,dtype=np.int8)
        sq[(x*x)%p]=1;sq[0]=0
        v=-int(sq[(x*x%p*x+A*x+B)%p].sum(dtype=np.int64))
        check(v*v<=4*p)
    pp=p; prev=1;cur=v
    while pp<=M:
        idx=np.arange(pp,M+1,pp);idx=idx[idx%(pp*p)!=0];a[idx]*=cur
        prev,cur=cur,v*cur-(0 if p in bad else p*prev);pp*=p
check(a[1]==1 and all(abs(int(a[n]))<=2*n for n in range(1,M+1)))
coeff=[int(v) for v in a]
# Machin formula with alternating rational bounds.
def atan_bounds(x):
    lo=sum((-1)**j*x**(2*j+1)/ (2*j+1) for j in range(24))
    return lo,lo+x**49/49
l,u=atan_bounds(Q(1,5));v,w=atan_bounds(Q(1,239))
pi_lo,pi_hi=16*l-4*w,16*u-4*v
S=10**24
root=isqrt(N*S*S)
c_lo=2*pi_lo*S/(root+1);c_hi=2*pi_hi*S/root
# Use smaller rational interval with modest denominators.
cl=Q(211318454543433,10**17);ch=Q(211318454543434,10**17)
check(cl<=c_lo<=c_hi<=ch)
# Return fixed-point enclosing interval for exp(-x) for rational x>=0.
def expneg(x):
    k=0
    while x>1: x/=2;k+=1
    term=Q(1);v=term
    for j in range(1,25): term=-term*x/j;v+=term
    lo=v-term*x/25;hi=v
    l=lo.numerator*S//lo.denominator;h=-((-hi.numerator*S)//hi.denominator)
    for _ in range(k): l=l*l//S;h=(h*h+S-1)//S
    return l,h

def qbound(t):
    return expneg(ch*t)[0],expneg(cl*t)[1]

# Horner interval using exact fixed-point outward rounding. q>=0.
def fbound(t):
    ql,qh=qbound(t);l=h=0
    for c in reversed(coeff):
        l=(l*(ql if l>=0 else qh))//S+c*S
        h=-((-h*(qh if h>=0 else ql))//S)+c*S
    return Q(l,S),Q(h,S)

# log(t) bounds via atanh series, reducing t to [1,2].
def log_unit(t):
    z=(t-1)/(t+1);z2=z*z;v=z;lo=Q(0)
    for j in range(20): lo+=2*v/(2*j+1);v*=z2
    return lo,lo+2*v/(41*(1-z2))
log2=log_unit(Q(2))
def logbound(t):
    k=0
    while t>2:t/=2;k+=1
    l,h=log_unit(t)
    # round outward to fixed denominator
    l+=k*log2[0];h+=k*log2[1]
    return Q(l.numerator*S//l.denominator,S), Q(-((-h.numerator*S)//h.denominator),S)

def q_hi(t): return Q(qbound(t)[1],S)
# Uniform omitted series tail at t=1, and integrated weighted tail over [1,infty).
# |a_n|<=2n and log(t)^2<=t for t>=1.
q=q_hi(Q(1))
# Avoid massive rational powers: fixed-point exponent upper rounded at each multiplication.
def power_upper(q,n):
    b=-((-q.numerator*S)//q.denominator);v=S
    while n:
        if n&1:v=(v*b+S-1)//S
        b=(b*b+S-1)//S;n//=2
    return Q(v,S)
r=power_upper(q,M+1)
point_tail=2*r*((M+1)/(1-q)+q/(1-q)**2)
int_tail=2*r*(1/cl+1/(cl*cl*(M+1)))/(1-q)
check(point_tail<Q(1,1000) and int_tail<1)
fl,fh=fbound(Q(1));check(fl-point_tail>0)
print('Fricke fixed point lower/upper:',float(fl-point_tail),float(fh+point_tail),flush=True)
# Midpoint rule on dyadic blocks. The second derivative estimate is for the
# truncated polynomial, all summands majorized by full geometric moments.
# Use 64 uniform intervals per octave, t in [1,2^14].
lo=hi=err=Q(0);K=64
for k in range(14):
    base=2**k;h=Q(base,K)
    for j in range(K):
        left=base+j*h;right=left+h;mid=left+h/2
        f0,f1=fbound(mid);ll,lh=logbound(mid)
        lo+=h*min(f0*ll*ll,f0*lh*lh);hi+=h*max(f1*ll*ll,f1*lh*lh)
        q=q_hi(left); d=1-q; L=logbound(right)[1]
        F0=2*q/d**2;F1=2*ch*q*(1+q)/d**3;F2=2*ch**2*q*(1+4*q+q*q)/d**4
        E=h**3/24*(2*(1+L)/left**2*F0+4*L/left*F1+L**2*F2)
        # Round sum terms outward to keep denominators bounded.
        err+=Q(-((-E.numerator*S)//E.denominator),S)
    # Round running midpoint sum only if necessary: denominators share fixed S^3.
    print('octave',k,'midpoint',float(lo),float(hi),'err',float(err),flush=True)
T=Q(2**14);q=q_hi(T)
# For t>=T, geometric bound |F(t)|<=2 exp(-cl t)/(1-q(T))^2.
late=2*q*(T/cl+1/cl**2)/(1-q)**2
check(late<1)
low=lo-err-int_tail-late;high=hi+err+int_tail+late
check(low>0)
print('weighted integral strict rational bounds (outward integers):',low.numerator//low.denominator,-((-high.numerator)//high.denominator))
print('quadrature bound',float(err),'late tail',float(late),'coefficient tail',float(int_tail))
print(f'{checks}/{checks} exact checks PASS')
