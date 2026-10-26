#!/usr/bin/env python3
"""Finite-depth Wilson-word nonidentifiability — exact source-first audit.

Original mathematical sources: Hatcher, Algebraic Topology Example 2B.2
(free stage F_(2^n) and commutator child expansion); Hatcher Example 1.21
(wedge of circles is free). PR #1244 owns 3-sector C3 source geometry
and a finite 2I simulator; PR #1247 owns the selected SU3 matrix;
#1249/#84 own its regularity consumers.

Derived NO-GO: for every finite depth n, the source stage
F_(3*2^n) and a tame rose with 3*2^n circles have the SAME
marked group. Every unitary generator assignment produces identical
stage words, ancestor commutators, Wilson spectra and traces. This
does not equate spaces, length, area, curvature, all-depth field
regularity or a measured wild-specific signal.
"""
from itertools import product

def red(w):
    a=[]
    for x in w:
        if a and a[-1]==-x:a.pop()
        else:a.append(x)
    return tuple(a)

def inv(w):return tuple(-x for x in w[::-1])
def comm(a,b):return red(a+b+inv(a)+inv(b))
def idx(s,bits,n):
    return 1+s*2**n+sum(b*2**j for j,b in enumerate(bits[::-1]))
def expand(s,w,n):
    if len(w)==n:return (idx(s,w,n),)
    return comm(expand(s,w+(0,),n),expand(s,w+(1,),n))
def rotation(w,n):
    m=2**n
    return tuple((1 if x>0 else -1)*
      (1+((abs(x)-1)//m+1)%3*m+(abs(x)-1)%m) for x in w)
for n in range(7):
    for s in range(3):
        for k in range(n+1):
            for w in product((0,1),repeat=k):
                v=expand(s,w,n)
                assert red(v)==v and len(v)==4**(n-k)
                assert rotation(v,n)==expand((s+1)%3,w,n)
                if k<n:
                    assert v==comm(expand(s,w+(0,),n),
                                   expand(s,w+(1,),n))
print("PASS exact free words and C3 sector naturality through depth 6")

# Any group-target map from the stage free group is determined by the
# 3*2^n leaf images. Those images can be assigned to a tame rose too.
# Matrices below are just an independent exact SU3 receiver control.
try:
    from sympy import Matrix,eye,I
    A=Matrix([[0,I,0],[I,0,0],[0,0,1]])
    B=Matrix([[0,1,0],[-1,0,0],[0,0,1]])
    E=eye(3)
    assert A.det()==B.det()==1 and A*A.H==B*B.H==E
    assert A*B*A.H*B.H!=E
    def eval_word(w,rep):
        out=E
        for i in w:out=out*(rep[abs(i)] if i>0 else rep[abs(i)].H)
        return out
    def eval_tree(s,w,n,rep):
        if len(w)==n:return rep[idx(s,w,n)]
        a=eval_tree(s,w+(0,),n,rep)
        b=eval_tree(s,w+(1,),n,rep)
        return a*b*a.H*b.H
    for n in range(5):
        rep={i:(A if i%2 else B) if i%3 else E
             for i in range(1,3*2**n+1)}
        for s in range(3):
            for k in range(n+1):
                for w in product((0,1),repeat=k):
                    assert eval_word(expand(s,w,n),rep)==eval_tree(s,w,n,rep)
    print("PASS exact independent SU3 finite Wilson matrices through depth 4")
except ImportError:
    print("SKIP optional SymPy SU3 check")

assert 3*4**5==3072 and 3*4**10==3145728
print("PASS exact three-sector word evaluation gate budgets depths 5,10")
print("FAIL-CLOSED: no source wild embedding, infinite-depth regularity or physical measurement")


# EXTENDABILITY discriminator (existing horn #1244's original
# AlexanderHornedAbelianHolonomyBIDIExact owner is cited, not
# reimplemented): at every depth>=1, any ancestor meridian is
# a nested commutator word; every generator exponent sum is 0.
# Therefore a nontrivial stage U1 character CANNOT be extended
# even one genuine Hatcher refinement step. The positive
# nonabelian all-stage existence uses original Goto 1949.
# Neither result makes a finite Wilson experiment wild-specific.
for n in range(1,7):
    for s in range(3):
        w=expand(s,(),n)
        assert all(sum((1 if x>0 else -1) for x in w
                       if abs(x)==j)==0
                   for j in range(1,3*2**n+1))
print("PASS abelian characters fail Hatcher one-step extension, depth1..6")
