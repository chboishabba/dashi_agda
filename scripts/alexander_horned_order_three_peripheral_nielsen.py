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
# Stronger exact based-path requirement for the selected ternary bonding word.
# phi(w) is conjugate by this PARTICULAR q, but not equal as a based word.
q=(3,-1,3,-1)  # c a^-1 c a^-1
assert subst(w,phi)==red(q+w+inv(q))
assert subst(w,phi)!=w

# Every FREELY REDUCED word of length <= 5: 1+6+30+150+750+3750=4687.
# This is a computational regression, not a quantified Agda kernel theorem.
from itertools import product
checks=0
alphabet=(-3,-2,-1,1,2,3)
for n in range(6):
    for letters in product(alphabet,repeat=n):
        if red(letters)!=letters:
            continue
        t=letters
        for _ in range(3):
            t=subst(t,phi)
        assert t==letters,(letters,t)
        checks+=1
assert checks==4687
print("PASS:",checks,"reduced free words length <=5 have phi^3=id")
print("PASS: exact based conjugator q=c A c A; strict based phi(w)=w FAILS")
# INTEGRAL MODULE OBSTRUCTION: phi and literal 3-cycle have matching
# characteristic polynomial t^3-1 but differ as Z[C3]-modules.
# GL3(Z) conjugacy would induce mod-3 conjugacy and preserve fixed counts.
N=((-1,-1,0),(1,0,0),(2,1,1))
P=((0,0,1),(1,0,0),(0,1,0))
def act(matrix,v):
    return tuple(sum(row[i]*v[i] for i in range(3))%3 for row in matrix)
V=list(product(range(3),repeat=3))
assert len(V)==27
n_fixed=[v for v in V if act(N,v)==v]
p_fixed=[v for v in V if act(P,v)==v]
assert len(n_fixed)==9,(len(n_fixed),n_fixed)
assert len(p_fixed)==3,(len(p_fixed),p_fixed)
assert all(act(N,act(N,act(N,v)))==v for v in V)
assert all(act(P,act(P,act(P,v)))==v for v in V)
print("PASS: 27/27 mod-3 vectors; Nielsen 9 fixed versus permutation 3 fixed")
print("NO-GO: actions cannot be GL3(Z) conjugate despite the same t^3-1")
print("PASS: nontrivial order-three Nielsen automorphism preserving [w] in F3")
print("Images: a -> c a^-1 c b; b -> a^-1 c; c -> c")
print("Geometric cap-relative realisation and Agda kernel are NOT established.")


# G4-COCYCLE-OBSTRUCTION: the chosen peripheral conjugator has a
# nontrivial threefold path-transfer norm, independently of a 3D model.
# Mathematical prior art: cyclic centralizers of non-power free-group
# elements, and the classical boundary twist/extension principle.
q=(3,-1,3,-1)
phi_q=subst(q,phi)
phi2_q=subst(phi_q,phi)
norm=red(phi2_q+phi_q+q)
assert norm==inv(w), (norm,inv(w))
def power(w,k):
    base=w if k>=0 else inv(w)
    out=()
    for _ in range(abs(k)):
        out=red(out+base)
    return out
def based_phi(word,conjugator=q):
    return red(inv(conjugator)+subst(word,phi)+conjugator)
assert based_phi(w)==w
for generator in (a,b,c):
    x=generator
    for _ in range(3):
        x=based_phi(x)
    assert x==red(w+generator+inv(w)), (generator,x)
assert based_phi(based_phi(based_phi(a)))!=a
# Any OTHER conjugator fixing the same cyclically reduced non-power
# parent must differ from q by w^k; the theorem giving this is the
# classical free-group centralizer result, not a finite search.
for k in range(-7,8):
    qk=red(q+power(w,k))
    assert subst(w,phi)==red(qk+w+inv(qk))
    norm_k=red(subst(subst(qk,phi),phi)+subst(qk,phi)+qk)
    assert norm_k==power(w,3*k-1), (k,norm_k)
    assert norm_k, k
print("PASS G4-COCYCLE-OBSTRUCTION: phi^2(q) phi(q) q = w^-1")
print("PASS G4-COCYCLE-OBSTRUCTION: based phi fixes w but cube = Inn(w) on 3 generators")
print("PASS G4-COCYCLE-OBSTRUCTION: k=-7..7 norms w^(3k-1), none trivial")
print("BOUNDARY: all-integer no-go uses classic centralizer/root theorem, not exhaustive k sampling")
print("BOUNDARY: Newman 1931 is a separate periodic cap-pointwise 3D obstruction")
