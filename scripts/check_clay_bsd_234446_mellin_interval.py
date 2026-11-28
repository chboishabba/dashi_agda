"""Original 234446.a1 Mellin jet enclosures, not an exact zero test.
Point counts/Hecke recurrence: existing check_clay_bsd_234446_two_crossings.py.
Classical modularity/Fricke, Hasse; new DASHI positive rational quadrature.
"""
from fractions import Fraction as Q
from math import factorial, isqrt
import sympy as sp
import numpy as np
N=234446; M=4000; S=10**30

def require(ok,msg):
    if not ok: raise AssertionError(msg)

def floor(x): return x.numerator//x.denominator
def ceil(x): return -floor(-x)

def trace(p):
    if p==2:return p-sum((y*y+x*y-x**3+x*x+79*x-289)%p==0 for x in range(p) for y in range(p))
    sq=[0]*p
    for x in range(1,p):sq[x*x%p]=1
    return sum(0 if (d:=(x*x+4*(x*x*x-x*x-79*x+289))%p)==0 else 1-2*sq[d] for x in range(p))

def coefficients():
    require(trace(2)==-1 and trace(117223)==1,'Fricke sign')
    ap={int(p):trace(int(p)) for p in sp.primerange(2,M+1)}
    cs=[]
    for n in range(1,M+1):
        a=1
        for p,e in sp.factorint(n).items():
            x,y=1,ap[p]
            for j in range(1,e):x,y=y,ap[p]*y-(0 if N%p==0 else p*x)
            a*=y
        cs.append(a)
    require(all(abs(a)<=2*n for n,a in enumerate(cs,1)),'coefficient check')
    return cs

def atan_bounds(k):
    lo=sum((Q((-1)**i,(2*i+1)*k**(2*i+1)) for i in range(24)),Q(0))
    return lo,lo+Q(1,49*k**49)

l,h=atan_bounds(5);u,v=atan_bounds(239)
pi_lo,pi_hi=16*l-4*v,16*h-4*u
z=isqrt(N*S*S)
c_lo=2*pi_lo/Q(z+1,S);c_hi=2*pi_hi/Q(z,S)
c_lo,c_hi=Q(floor(c_lo*S),S),Q(ceil(c_hi*S),S)
R=Q(988,1000)
require(sum(c_lo**j/factorial(j) for j in range(5))>1/R,'q bound')

def exp_neg(x):
    k=0
    while x>Q(1,8):x/=2;k+=1
    a=sum(((-x)**j/factorial(j) for j in range(18)),Q(0))
    lo,hi=floor(S*a),ceil(S*(a+x**18/factorial(18)))
    for _ in range(k):lo,hi=lo*lo//S,-(-hi*hi//S)
    return lo,hi

def log_unit(x):
    t=(x-1)/(x+1)
    require(0<=t<=Q(1,3),'log range')
    def series(t):
        v=t; a=Q(0)
        for j in range(26):a+=2*v/(2*j+1);v*=t*t
        return a,2*v/(53*(1-t*t))
    tl,th=Q(floor(t*S),S),Q(ceil(t*S),S)
    a,_=series(tl);b,e=series(th)
    return floor(a*S),ceil((b+e)*S)

LOG2=log_unit(Q(2))
def log_bounds(x):
    k=0
    while x>=2:x/=2;k+=1
    l,h=log_unit(x)
    return l+k*LOG2[0],h+k*LOG2[1]

def f_bounds(cs,y):
    ql=exp_neg(c_hi*y)[0];qh=exp_neg(c_lo*y)[1]
    lo=hi=0
    for a in reversed(cs):
        p=(lo*ql,lo*qh,hi*ql,hi*qh)
        lo=min(p)//S+a*S;hi=-(-max(p)//S)+a*S
    p=(lo*ql,lo*qh,hi*ql,hi*qh)
    return min(p)//S,-(-max(p)//S)

def quadrature():
    # Floating roots are only proposals; all weights/moments checked exactly.
    nodes,_=np.polynomial.legendre.leggauss(28)
    pos=[Q(round(float(x)*10**10),10**10) for x in nodes if x>0]
    A=sp.Matrix(14,14,lambda i,j:sp.Rational(pos[j])**(2*i))
    weights=[Q(w) for w in A.inv()*sp.Matrix([sp.Rational(1,2*i+1) for i in range(14)])]
    require(all(w>0 for w in weights),'positive weights')
    pairs=[(sign*x,w) for x,w in zip(pos,weights) for sign in (-1,1)]
    for k in range(28):require(sum(w*x**k for x,w in pairs)==(Q(2,k+1) if k%2==0 else 0),'moment exactness')
    return pairs

def run():
    cs=coefficients();pairs=quadrature();tot={2:[Q(0),Q(0)],4:[Q(0),Q(0)]};err={2:Q(0),4:Q(0)}
    a=Q(1);panels=0
    while a<4096:
        b=5*a/4;m=(a+b)/2;h=(b-a)/2
        require(m<8192,'log disk bound')
        for x,w in pairs:
            y=m+h*x;fl,fh=f_bounds(cs,y);ll,lh=log_bounds(y)
            for k in tot:
                v=[Q(f*lg**k,S**(k+1)) for f in (fl,fh) for lg in (ll,lh)]
                tot[k][0]+=h*w*min(v);tot[k][1]+=h*w*max(v)
        # Disk radius m/2, log magnitude <= log m+1 <=14.
        for k in tot:
            B=8*14**k/(c_lo*m)**2
            err[k]+=2*(b-a)*B*Q(2,9)**28/(1-Q(2,9))
        a=b;panels+=1
    require(c_lo*(M+1)>8,'integrated tail guard')
    coeff_tail=4/c_lo*R**(M+1)/(1-R)
    e=Q(exp_neg(c_lo*a)[1],S)
    require(e<Q(1,2),'far tail guard')
    for k in tot:
        far=8*e*sum(Q(factorial(k),factorial(k-j))*a**(k-j)/c_lo**(j+1) for j in range(k+1))
        margin=err[k]+coeff_tail+far
        lo,hi=tot[k][0]-margin,tot[k][1]+margin
        print('Mellin log power',k,'outward 1e-12 interval',floor(lo*10**12),ceil(hi*10**12),'error budget',float(margin),flush=True)
        if k==2:require(lo<0<hi and hi-lo<Q(1,10**6),'near-zero interval, not equality')
        else:require(lo>0,'positive fourth jet')
    print('panels',panels,'positive rational 28-node quadrature PASS',flush=True)

if __name__=='__main__':run()
