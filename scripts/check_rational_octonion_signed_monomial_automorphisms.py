#!/usr/bin/env python3
from itertools import permutations

# Cayley-Dickson convention used by RationalOctonion:
#   (a,b)(c,d) = (ac - conjugate(d)b, da + b conjugate(c)).
# This script reconstructs the multiplication table on e1,...,e7,
# enumerates all signed basis permutations preserving multiplication,
# and checks the two explicit generators used by the Agda owner.

def qmul(a,b):
    a0,a1,a2,a3=a; b0,b1,b2,b3=b
    return (
        a0*b0-a1*b1-a2*b2-a3*b3,
        a0*b1+a1*b0+a2*b3-a3*b2,
        a0*b2-a1*b3+a2*b0+a3*b1,
        a0*b3+a1*b2-a2*b1+a3*b0,
    )

def qconj(a): return (a[0],-a[1],-a[2],-a[3])
Z=(0,0,0,0)

def omul(x,y):
    a,b=x; c,d=y
    ac=qmul(a,c); cdb=qmul(qconj(d),b)
    first=tuple(u-v for u,v in zip(ac,cdb))
    da=qmul(d,a); bc=qmul(b,qconj(c))
    second=tuple(u+v for u,v in zip(da,bc))
    return first,second

B=[((1,0,0,0),Z),((0,1,0,0),Z),((0,0,1,0),Z),((0,0,0,1),Z),
   (Z,(1,0,0,0)),(Z,(0,1,0,0)),(Z,(0,0,1,0)),(Z,(0,0,0,1))]

def v8(o): return o[0]+o[1]
M={}
for i in range(1,8):
    for j in range(1,8):
        nz=[(k,c) for k,c in enumerate(v8(omul(B[i],B[j]))) if c]
        assert len(nz)==1
        k,s=nz[0]
        M[i,j]=(s,k)

def is_auto(p,s):
    for i in range(1,8):
        for j in range(1,8):
            sg,k=M[i,j]
            sg2,k2=M[p[i-1],p[j-1]]
            expected_k=0 if k==0 else p[k-1]
            lhs=s[i-1]*s[j-1]*sg2
            rhs=sg if k==0 else sg*s[k-1]
            if k2 != expected_k or lhs != rhs:
                return False
    return True

autos=[]
for p in permutations(range(1,8)):
    for mask in range(1<<7):
        s=tuple(-1 if (mask>>(i-1))&1 else 1 for i in range(1,8))
        if is_auto(p,s): autos.append((p,s))
assert len(autos)==1344

ID=(tuple(range(1,8)),(1,)*7)
def compose(g,h):
    p,s=g; q,t=h # g after h
    r=tuple(p[q[i-1]-1] for i in range(1,8))
    u=tuple(t[i-1]*s[q[i-1]-1] for i in range(1,8))
    return r,u

def closure(gens):
    seen={ID}; todo=[ID]
    while todo:
        a=todo.pop()
        for g in gens:
            b=compose(g,a)
            if b not in seen:
                seen.add(b); todo.append(b)
    return seen

def order(g):
    x=ID
    for n in range(1,100):
        x=compose(g,x)
        if x==ID: return n
    raise AssertionError('order too large')

# e_i -> sign[i] e_perm[i]
G7=((2,4,6,3,1,7,5),(1,-1,-1,1,1,1,1))
G2=((1,2,3,5,4,7,6),(-1,1,-1,1,1,1,1))
assert is_auto(*G7) and order(G7)==7
assert is_auto(*G2) and order(G2)==2
G=closure([G7,G2])
assert len(G)==1344
assert G==set(autos)
print('signed-monomial octonion automorphisms:',len(autos))
print('generator orders:',order(G7),order(G2))
print('generated closure:',len(G))
print('PASS')
