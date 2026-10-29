#!/usr/bin/env python3
"""Exact ternary peripheral order-three Nielsen automorphism; no 3D claim."""
def red(w):
    s=[]
    for x in w:
        if s and s[-1]==-x: s.pop()
        else: s.append(x)
    return tuple(s)
def inv(w): return tuple(-x for x in reversed(w))
def subst(w, images):
    return red(x for g in w for x in (images[abs(g)] if g>0 else inv(images[abs(g)])))
def cyclic(w):
    a=list(red(w))
    while len(a)>1 and a[0]==-a[-1]: a=a[1:-1]
    return tuple(a)
def conjugate(a,b):
    a,b=cyclic(a),cyclic(b)
    return len(a)==len(b) and any(a==b[k:]+b[:k] for k in range(len(b)))
a,b,c=(1,),(2,),(3,)
u,v,z=(-2,),(-3,1),(3,)
comm=lambda x,y:red(x+y+inv(x)+inv(y))
w=red(comm(a,b)+comm(b,c))
p=red(a+b+inv(a)+c)
assert w==red(p+comm(u,v)+inv(p))
phi={1:(3,-1,3,2), 2:(-1,3), 3:(3,)}
assert subst(u,phi)==v
assert subst(v,phi)==red(inv(v)+inv(u))
assert subst(z,phi)==z
for g in (1,2,3):
    t=(g,)
    for _ in range(3): t=subst(t,phi)
    assert t==(g,)
assert phi[1]!=(1,)
assert conjugate(subst(w,phi),w)
assert not conjugate(subst(w,phi),inv(w))
print("PASS: nontrivial order-three Nielsen automorphism preserving [w] in F3")
print("Images: a -> c a^-1 c b; b -> a^-1 c; c -> c")
print("Geometric cap-relative realisation and Agda kernel are NOT established.")
