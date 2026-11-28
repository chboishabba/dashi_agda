from itertools import product
from collections import Counter
from math import isqrt
import sympy as s

# Independent exact diagnostic of the native affine charts and Lean signed
# residual. Does not execute Agda or Lean.
def H(x):
    a,b,c,d=x
    return (a+b+c+d,a+b-c-d,a-b+c-d,a-b-c+d)
def N(x): return sum(t*t for t in x)
def I(x):
    k,b,c,d=x
    return (2*k+1-b-c-d,b,c,d)
def E(x,p=0):
    j,u,v,w=x
    a,b,c=2*u+1,2*v+1,2*w+1
    return a,b,c,4*j+p-a-b-c
def enc(x):
    k,b,c,d=x
    return 2*k+1-b-c-d,k,k-c-d,k-b-d
def dec(x):
    j,u,v,w=x
    return u,u+v+1-j,u+w+1-j,j-v-w-1
def flip(x): return (-x[0],*x[1:])
def ep(x):
    j,u,v,w=x
    return j-u-1,-u-1,v,w
def pe(x):
    j,u,v,w=x
    return j-u,-u-1,v,w

def checks(x):
    return [tuple(a-b for a,b in zip(enc(dec(x)),x)),tuple(a-b for a,b in zip(dec(enc(x)),x)),tuple(a-b for a,b in zip(ep(pe(x)),x)),tuple(a-b for a,b in zip(pe(ep(x)),x)),tuple(a-b for a,b in zip(H(I(x)),E(enc(x)))),tuple(a-b for a,b in zip(H(E(x)),[4*t for t in I(dec(x))])),tuple(a-b for a,b in zip(flip(E(x)),E(ep(x),2))),(N(H(x))-4*N(x),N(flip(x))-N(x))]
x=s.symbols('a b c d',integer=True)
n=0
for v in checks(x):
    for r in v:
        assert s.expand(r)==0
        n+=1
A,B,C,z=s.symbols('A B C z')
R=B-A-C
assert s.expand(R.subs({A:-z*z*C,B:-z*z*B,C:-z*z*A},simultaneous=True)+z*z*R)==0;n+=1
assert s.expand(R.subs({A:-A,B:C,C:B},simultaneous=True)+R)==0;n+=1
Q=A*A-A*B+B*B;W=(A+B)*(2*A-B)*(A-2*B);V=A*B*(B-A)
assert s.expand((A*A+B*B+(B-A)**2)/2-Q)==0;n+=1
assert s.expand((A+B)*(B+B-A)*(B-2*A)-W)==0;n+=1
assert s.expand(4*Q**3-W**2-27*V**2)==0;n+=1
print('symbolic',n)
m=0
for x in product(range(-5,6),repeat=4):
    for v in checks(x):
        assert all(a==0 for a in v);m+=len(v)
print('affine chart',m)
# Independently exhaust actual raw shells, not just chart samples.
L=64
integer=Counter();half=Counter()
for x in product(range(-isqrt(L),isqrt(L)+1),repeat=4):
    k=N(x)
    if k<=L:
        integer[k]+=1
        if k%2:
            y=H(x)
            assert all(a%2 for a in y) and sum(y)%4==0 and N(y)==4*k
            assert tuple(a//4 for a in H(y))==x
for y in product(range(-2*isqrt(L)+1,2*isqrt(L),2),repeat=4):
    k=N(y)
    if k<=4*L and k%4==0:
        half[k//4]+=1
        j,u,v,w=sum(y)//4,*((t-1)//2 for t in y[:3])
        p=sum(y)%4
        assert E((j,u,v,w),p)==y
        x=(j,u,v,w) if p==0 else pe((j,u,v,w))
        x=I(dec(x))
        assert N(x)==k//4 and sum(x)%2==1
for k in range(L+1):
    assert half[k]==(1-(-1)**k)*integer[k]
print('shell degrees',L+1,'integer points',sum(integer.values()),'half points',sum(half.values()))
