"""Exact alias separation and fourth-difference controls for the projected return.
Actual level-one residues from the committed original-symbol certificate;
no new cusp evaluation, Archimedean zero test or BSD proof.
"""
from math import gcd
import sympy as sp
X=sp.Symbol('X')
checks=0

def ck(ok):
    global checks
    if not ok: raise AssertionError('projected return control failed')
    checks+=1

def roots(p,n):
    r=list(range(1,p)); h=p
    for _ in range(1,n):
        r=[a+b*h for a in r for b in range(p) if pow(a+b*h,p-1,h*p)==1]
        h*=p
    ck(len(r)==p-1 and len(set(r))==p-1)
    return r

def homogeneous(d,a,b):
    f=sp.Poly(sp.cyclotomic_poly(d,X),X)
    return sum(int(c)*a**(f.degree()-i)*b**i for i,c in enumerate(f.all_coeffs()))

# Every non-rational tame multiplier has a nonzero homogeneous norm.
for p in (5,11):
    for n in range(2,11):
        q=p**n; h=q//p
        rr=roots(p,n)
        for z in rr:
            if z in (1,q-1):continue
            d=next(i for i in range(1,p) if pow(z,i,q)==1)
            degree=int(sp.totient(d));ck(degree==(2 if p==5 else 4))
            for k in range(1,65):
                if k%p==0:continue
                for b in (k,-k):
                    a=b*z%h
                    norm=homogeneous(d,a,b)
                    ck(norm!=0 and norm%h==0)
                    ck((a+abs(b))**degree>=abs(norm)>=h)

# Exact original projected residues from the prior actual 244-symbol replay.
# Work at m=1 modulo p, where X^p-1=(X-1)^p.
for p,ds in ((5,[1,1,1,1,1]),(11,[4,7,0,7,7,7,7,0,7,4,5])):
    f=sp.Poly(sum(a*X**i for i,a in enumerate(ds)),X,modulus=p)
    t=sp.Poly((X-1)**4,X,modulus=p)
    u,r=divmod(f,t);ck(r.is_zero and u.eval(1)%p!=0)
    ck(u.eval(1)%p==(1 if p==5 else 2))
    # Verify transpose of the actual fourth difference on all coordinate tests.
    a=[int(u.nth(i)) for i in range(p)]
    from math import comb
    for j in range(p):
        rhs=sum(a[k]*sum((-1)**(4-i)*comb(4,i)*int((k+i)%p==j) for i in range(5)) for k in range(p))
        ck(rhs%p==ds[j])
    print('p',p,'actual mod-p unit quotient',u.as_expr(),flush=True)

# A single even additive Fourier mode survives the real multiplicative
# fourth difference. Check the exact projected mode at the original levels.
# These are kernel mode controls, not evaluations of the full Mellin kernel.
for p,n in ((5,2),(5,3),(11,2)):
    q=p**n; h=q//p; rr=roots(p,n); g=1+p
    def red(v):
        return [v[i+j*h]-v[i+(p-1)*h] for j in range(p-1) for i in range(h)]
    nonzero=0
    for k in range(h):
        a=pow(g,k,q); v=[0]*q
        for i in range(5):
            for z in rr:
                b=z*a*pow(g,i,q)%q
                v[b]+=(-1)**(4-i)*comb(4,i)
                v[-b%q]+=(-1)**(4-i)*comb(4,i)
        nonzero+=any(red(v))
    ck(nonzero>0)
    print('p,n',p,n,'nonzero projected fourth-difference mode addresses',nonzero,'of',h,flush=True)
print(f'{checks}/{checks} exact controls PASS',flush=True)
