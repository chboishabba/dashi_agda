#!/usr/bin/env python3
"""Dust/Noise x Sophontic: exact finite probe and paired-intervention certificates.
No external packages. This verifies *finite identities*, not ML benchmark claims.
Source roots: Q Labs Dust/Noise; Sophontic geometric reasoning paired flip-rate.
"""
from fractions import Fraction as Q
from itertools import product
from math import prod

def parity(n):
    return n.bit_count() & 1

def hadamard(n):
    assert n >= 1 and n & (n-1) == 0
    return [[(-1) ** parity(i & j) for j in range(n)] for i in range(n)]

def dot(a,b):
    return sum(x*y for x,y in zip(a,b))

def matvec(A,x):
    return [dot(row,x) for row in A]

def exact_linear_credit(H,c,offset,x,sigma):
    """Sum directional one-sided differences; exact for affine f."""
    n=len(c)
    f=lambda z:dot(c,z)+offset
    y=[f([x[j]+sigma*H[i][j] for j in range(n)])-f(x) for i in range(n)]
    return [sum(y[i]*H[i][j] for i in range(n))/(n*sigma) for j in range(n)]

def test_hadamard():
    # Exhaustively prove sampled small-instance matrix certificates.
    for n in (1,2,4,8,16):
        H=hadamard(n)
        assert all(dot(H[i],H[j]) == (n if i==j else 0)
                   for i in range(n) for j in range(n))
        for k in range(n):
            c=[Q((j*3+k)%7-3) for j in range(n)]
            x=[Q(j-2,3) for j in range(n)]
            assert exact_linear_credit(H,c,Q(7,5),x,Q(1,13))==c
    print("PASS Walsh orthogonality and affine credit recovery: n=1,2,4,8,16")

def test_nonlinear_bias():
    # f(x) = x^3 in one dimension: central estimator = 3x²+sigma².
    for x,s in product([Q(-3),Q(-1,2),Q(0),Q(5,4)], [Q(1,10),Q(1,2)]):
        f=lambda z:z*z*z
        estimate=(f(x+s)-f(x-s))/(2*s)
        assert estimate-3*x*x == s*s
    print("PASS central difference cubic O(sigma²) exact bias identity")

def test_semantic_pairs():
    # Synthetic fixture: load-bearing fact flips reference answer.
    # Tests distinguish correct flip from both-answer-constant and both-answer-flip.
    rails=[(False, False), (True,True)]
    correct=lambda b:b
    static=lambda b:False
    invert=lambda b:not b
    def metrics(model):
        accuracy=sum(model(f)==a for f,a in rails)/len(rails)
        flips=(model(rails[0][0]) != model(rails[1][0]))
        # paired correctness demands BOTH items correct, not flip alone
        pair_ok=all(model(f)==a for f,a in rails)
        return accuracy,flips,pair_ok
    assert metrics(correct)==(1.0,True,True)
    assert metrics(static)==(0.5,False,False)
    assert metrics(invert)==(0.0,True,False)
    print("PASS paired flip != paired correctness; synthetic discriminator")

if __name__=="__main__":
    test_hadamard()
    test_nonlinear_bias()
    test_semantic_pairs()
