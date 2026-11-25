"""Exact algebra/interval regressions, not universal Clay proofs or kernels."""
from fractions import Fraction as Q
from itertools import permutations
import sympy as S

def need(x):
    if not x: raise ArithmeticError('failed')

# NS: second Volterra resolvent, including coalescent rates.
a,b,h=S.symbols('a b h', positive=True)
W=(1-S.exp(-a*h))/a
L=( (1-S.exp(-b*h))/b-(S.exp(-a*h)-S.exp(-b*h))/(b-a) )/a
Lsame=((1-S.exp(-a*h))/a-h*S.exp(-a*h))/a
need(S.simplify(S.diff(L,h)+b*L-W)==0)
need(S.simplify(L.subs(h,0))==0)
need(S.simplify(S.diff(Lsame,h)+a*Lsame-W)==0)
need(S.simplify(Lsame.subs(h,0))==0)
print('NS Volterra identities 4')

# BSD: 389a1, rational interval integration of f(it/sqrt(389)) log(t)^2.
# c=2*pi/sqrt(389) between 31856/100000 and 31858/100000, using 3.14159<pi<3.14160.
cl,ch=Q(31856,100000),Q(31858,100000)
need(cl*cl*389<4*Q(314159,100000)**2 and ch*ch*389>4*Q(314160,100000)**2)
N=64; A=[0]*(N+1); A[1]=1
ap={}
for p in list(S.primerange(2,N+1)):
    ap[int(p)]=int(p)-sum((y*y+y-x*x*x-x*x+2*x)%p==0 for x in range(p) for y in range(p))
for n in range(2,N+1):
    v=1
    for p,k in S.factorint(n).items():
        p=int(p); u,w=1,ap[p]
        for j in range(2,k+1): u,w=w,ap[p]*w-p*u
        v*=w
    A[n]=v
need(A[1:20]==[1,-2,-2,2,-3,4,-5,0,1,6,-4,-4,-3,10,6,-4,-6,-2,5])
# Directed fixed-point enclosures, scale D. Exact integer rounding.
D=10**18; step=32
floor=lambda x: x.numerator*D//x.denominator
ceil=lambda x: -((-x.numerator*D)//x.denominator)
def expneg(x):
    # x between 0 and 1; odd/even alternating Taylor bounds.
    t=Q(1); s=t
    for j in range(1,22):
        t*=-x/j; s+=t
    return s,s-t
ql=floor(expneg(ch/step)[0]); qh=ceil(expneg(cl/step)[1])
# q^i for all endpoints and n<=64, with directed rounding at every product.
lo=[D]; hi=[D]
for i in range(16*step*N):
    lo.append(lo[-1]*ql//D); hi.append((hi[-1]*qh+D-1)//D)
def logseries(x):
    z=(x-1)/(x+1); t=z; s=Q(0)
    for j in range(24):
        s+=2*t/(2*j+1); t*=z*z
    return s,s+2*t/(49*(1-z*z))
l2,u2=logseries(Q(2))
def logbounds(x):
    k=0
    while x>=2: x/=2; k+=1
    l,u=logseries(x); return l+k*l2,u+k*u2
# Uniform coefficient tail at t>=1, q<3/4, |a_n|<=2n.
q=Q(3,4); tail=ceil(2*q**(N+1)*((N+1)-N*q)/(1-q)**2)
need(hi[step]<3*D//4)
logs=[]
for i in range(step,16*step+1):
    l,u=logbounds(Q(i,step)); logs.append((floor(l),ceil(u)))
area=0
for i in range(step,16*step):
    fmin=-tail; fmax=tail
    for n in range(1,N+1):
        if A[n]>=0: fmin+=A[n]*lo[(i+1)*n]; fmax+=A[n]*hi[i*n]
        else: fmin+=A[n]*hi[i*n]; fmax+=A[n]*lo[(i+1)*n]
    l=logs[i-step][0]; u=logs[i-step+1][1]
    area+=min(fmin*l*l,fmin*u*u,fmax*l*l,fmax*u*u)
# Beyond t=16, q<=1/8, leading coefficient dominates all subsequent coefficients.
need(hi[16*step]<D//8 and 2*(1/(1-Q(1,8))**2-1)<1)
bound=Q(area,step*D**3)
need(bound>0)
print('BSD prime coefficients',len(ap),'rectangles',15*step,'positive integral lower',float(bound))

# Hodge: primitive alternating forms on symplectic H^1 of a polarized abelian surface.
J=S.diag(S.Matrix([[0,1],[-1,0]]),S.Matrix([[0,1],[-1,0]]))
def B(i,j):
    a=S.zeros(4);a[i,j]=1;a[j,i]=-1;return a
M=[J.inv()*b for b in [B(0,1)-B(2,3),B(0,2),B(0,3),B(1,2),B(1,3)]]
need(all(S.trace(x)==0 and x.T*J==J*x for x in M))
z=0
for p in permutations(range(5)):
    w=S.eye(4)
    for j in p:w=w*M[j]
    z+=(-1)**sum(p[i]>p[j] for i in range(5) for j in range(i+1,5))*S.trace(w)
need(z==-120)
print('Hodge alternating symplectic trace',z,'normalized',z/120,'permutations 120')
