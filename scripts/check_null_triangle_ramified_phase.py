from itertools import product
from collections import Counter
from fractions import Fraction as F
import sympy as s

def require(ok):
    if not ok: raise AssertionError('ramified phase check failed')
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def neg(a): return tuple(-x for x in a)
def sub(a,b): return add(a,neg(b))
def gm(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def scale(a,k): return tuple(k*x for x in a)
# a+b*pi, Gaussian coefficients; pi^2=-3-3*pi
Z=(0,0); O=(1,0); I=(0,1)
zero=Z+Z; one=O+Z; ii=I+Z; pi=Z+O; rho=O+O

def mul(x,y):
    a,b=x[:2],x[2:]; c,d=y[:2],y[2:]; bd=gm(b,d)
    return add(gm(a,c),scale(bd,-3))+add(add(gm(a,d),gm(b,c)),scale(bd,-3))
def power(x,n):
    z=one
    for _ in range(n): z=mul(z,x)
    return z
def v3(x):
    x=F(x)
    if not x: return float('inf')
    def vp(n):
        k=0
        while n%3==0: n//=3; k+=1
        return k
    return vp(x.numerator)-vp(x.denominator)
def vg(a): return min(map(v3,a))
def v(x): return min(2*vg(x[:2]),2*vg(x[2:])+1)
def norm(x):
    a,b=x[:2],x[2:]; return add(sub(gm(a,a),scale(gm(a,b),3)),scale(gm(b,b),3))
def digit(x): return tuple((int(t)+1)%3-1 for t in x[:2])
def div_pi(x):
    a,b=x[:2],x[2:]
    require(all(t%3==0 for t in a))
    return sub(b,a)+tuple(-t//3 for t in a)
def decode(ds):
    z=zero
    for r in reversed(ds): z=add(r+Z,mul(pi,z))
    return z
def encode(x,n):
    ds=[]
    for _ in range(n):
        r=digit(x); ds.append(r); x=div_pi(sub(x,r+Z))
    return tuple(ds),x

# Symbolic relative norm identity and uniformizer multiplication.
a,b,c,d=s.symbols('a b c d'); N=lambda a,b:a*a-3*a*b+3*b*b
require(s.expand(N(a*c-3*b*d,a*d+b*c-3*b*d)-N(a,b)*N(c,d))==0)
require(mul(pi,pi)==scale(add(one,pi),-3))
require(power(ii,4)==one and power(ii,2)==neg(one))
require(power(rho,3)==one and rho!=one)
phase=mul(ii,rho); orbit=[power(phase,k) for k in range(12)]
require(len(set(orbit))==12 and power(phase,12)==one)
phase_pairs=Counter(v(sub(x,y)) for x,y in product(orbit,repeat=2))
require(phase_pairs=={float('inf'):12,1:24,0:108})
for x,y in product(orbit,repeat=2):
    require(v(sub(mul(phase,x),mul(phase,y)))==v(sub(x,y)))
# Field valuation and strict triangle on rational representatives.
points=list(product((-3,-1,0,1,3),repeat=4)); pairs=0
for x in points:
    require(v(x)==vg(norm(x)))
    for y in points:
        vx,vy=v(x),v(y); vz=v(add(x,y))
        require(vz>=min(vx,vy) and (vx==vy or vz==min(vx,vy)))
        require(v(mul(x,y))==vx+vy)
        pairs+=1
# All pi-adic address residues through depth 3; all depth-2 ordered pairs.
D=list(product((-1,0,1),repeat=2)); sizes=[]; residue_pairs=0
for n in range(1,4):
    ds=list(product(D,repeat=n)); values=[decode(w) for w in ds]
    require(len(set(values))==9**n)
    for w,x in zip(ds,values):
        enc,tail=encode(x,n); require(enc==w and tail==zero)
        require(encode(x,n-1)[0]==w[:-1])
    sizes.append(len(values))
    if n<=2:
        for (w,x),(u,y) in product(zip(ds,values),repeat=2):
            j=next((k for k,(r,t) in enumerate(zip(w,u)) if r!=t),float('inf'))
            require(v(sub(x,y))==j); residue_pairs+=1
# Low-digit refinement L_r(z)=r+pi*z scales distances, commutes with
# phase action only with digit and carry transported, not naively.
for r,z in product(D,orbit):
    x=add(r+Z,mul(pi,z)); y=mul(phase,x)
    r2=digit(mul(phase,r+Z)); carry=div_pi(sub(mul(phase,r+Z),r2+Z))
    require(y==add(r2+Z,mul(pi,add(carry,mul(phase,z)))))
require(mul(phase,one)!=digit(mul(phase,one))+Z)
print(f'PASS {pairs} valuation pairs; phase histogram {phase_pairs}; residue sizes {sizes}; {residue_pairs} residue pairs; 108 phase/refinement carry squares')
