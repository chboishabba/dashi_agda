#!/usr/bin/env python3
"""DASHI Alexander-Hatcher / gamma / Pickover cross-lane exact audit.

CREDITS: Euler/Legendre Gamma(n+1)=n!, elementary CRT/Legendre
valuations, Hatcher's separate classical horn complement, Galois/Jordan
A5 perfectness. DASHI PR #1260 and #1244 retain their original
independent producer and proof ownership. No same-object leap.
NO PI-REAL SIGN CERTIFICATE IS PRODUCED.

This file is a replay of only integer/factorial/CRT and finite group
facts. Python execution is not Agda/Lean kernel verification.
"""
from itertools import permutations, product
from math import factorial

def p_valuation_factorial(n, p):
    acc = 0
    while n:
        n //= p
        acc += n
    return acc

def perm_compose(p,q):
    return tuple(p[q[i]] for i in range(len(p)))

def inv(p):
    return tuple(p.index(i) for i in range(len(p)))

def parity(p):
    return sum(p[i]>p[j] for i in range(len(p))
               for j in range(i+1,len(p)))%2

def comm(p,q):
    return perm_compose(perm_compose(perm_compose(p,q),inv(p)),inv(q))

def closure(generators, n):
    identity=tuple(range(n))
    result={identity}
    pending=[identity]
    while pending:
        x=pending.pop()
        for g in generators:
            y=perm_compose(x,g)
            if y not in result:
                result.add(y)
                pending.append(y)
    return result

def main():
    # Gamma(10000)=9999! is a classical ANALYTIC extension theorem,
    # not numerically computed Gamma(10000), which would overflow.
    n=9999
    k=factorial(n)
    assert k>0 and k%2==0
    assert factorial(10000)==10000*k
    assert k.bit_length()==118445
    valuations={p:p_valuation_factorial(n,p) for p in (2,3,5,11,101)}
    assert valuations=={2:9991,3:4996,5:2495,11:998,101:99}

    # The exact giant INTEGER is never materialized. Python's modular pow
    # takes big integer exponent and tiny residue moduli.
    residues={d:pow(99,k,d) for d in (9,11,101,360,9999)}
    assert residues=={9:0,11:0,101:1,360:81,9999:4950}
    assert (4950*4950)%9999==4950
    assert (99*99)%360==81 and (81*99)%360==99
    assert (99*81)%360==99
    # Degree conversion: 81 degrees is in the positive sine semicircle.
    assert 0 < residues[360] < 180
    # Radians: M mod 360 is NOT M mod (2*pi).
    # We DO NOT test or claim the sign of sin(99^(9999!)) in radians.

    p5=tuple(permutations(range(5)))
    a5={p for p in p5 if parity(p)==0}
    assert len(p5)==120 and len(a5)==60
    abc={(p[:3],parity(p)):p for p in p5}
    assert len(abc)==120 and len({p[:3] for p in p5})==60
    # Prior A5 commutator generators can be recovered within A5.
    A=(1,2,0,3,4)
    B=(0,1,3,4,2)
    assert comm(comm(A,B),comm(inv(A),inv(B)))==A
    generated=closure((A,B),5)
    assert generated==a5
    assert closure({comm(x,y) for x in a5 for y in a5},5)==a5

    # Distinguish S5 order 120 from binary icosahedral 2I order 120.
    # S5 has nontrivial parity C2 quotient. 2I is classically perfect
    # and has a nontrivial centre, unlike S5. Equal order != isomorphism.
    odd=(1,0,2,3,4)
    assert parity(odd)==1
    assert all(parity(perm_compose(p,q))==(parity(p)+parity(q))%2
               for p in p5 for q in p5)

    print("PASS: exact factorial exponent, Gamma(10000) recurrence index,")
    print("      valuation(9999!) =",valuations)
    print("      M mod 9,11,101,360,9999 =",residues)
    print("      81 degrees => positive sine; radians => NOT DETERMINED")
    print("      S5=120; A5=60 perfect finite; triple×parity=60×2")
    print("      A,B overlapping 3-cycles recover commutator")
    print("BOUNDARY: no complex continuation/π phase/sign certificate")
    print("BOUNDARY: no constructed wild exterior and no Monster same-object")

if __name__=="__main__":
    main()
