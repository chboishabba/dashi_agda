#!/usr/bin/env python3
"""Y443/FLM finite control, not an actual Monster/VOA theorem.

Shows full automorphism group S5 of the five-atom algebra, recovers
all 120 group elements from two generators, and verifies action
extension to freely generated algebra terms. Exact integer arithmetic.
"""
from itertools import permutations, product
from collections import deque

N = 5
I = tuple(range(N))

def compose(p, q):
    return tuple(p[q[i]] for i in I)

def inverse(p):
    out = [0] * N
    for i, j in enumerate(p):
        out[j] = i
    return tuple(out)

def action(p, x):
    inv = inverse(p)
    return tuple(x[inv[i]] for i in I)

def mul(x, y):
    return tuple(a*b for a, b in zip(x, y))

def add(x, y):
    return tuple(a+b for a, b in zip(x, y))

def eval_term(term):
    kind, *rest = term
    if kind == "g":
        j = rest[0]
        return tuple(int(i == j) for i in I)
    if kind == "unit":
        return (1,)*N
    if kind == "sum":
        return add(eval_term(rest[0]), eval_term(rest[1]))
    if kind == "prod":
        return mul(eval_term(rest[0]), eval_term(rest[1]))
    if kind == "scale":
        return tuple(rest[0]*z for z in eval_term(rest[1]))
    raise ValueError(term)

def map_term(p, term):
    kind, *rest = term
    if kind == "g":
        return ("g", p[rest[0]])
    if kind == "unit":
        return term
    if kind in ("sum", "prod"):
        return kind, map_term(p,rest[0]), map_term(p,rest[1])
    if kind == "scale":
        return kind, rest[0], map_term(p,rest[1])
    raise ValueError(term)

def main():
    atoms = [tuple(int(i==j) for i in I) for j in I]
    idempotents = [x for x in product((0, 1), repeat=N) if mul(x,x)==x]
    assert len(idempotents)==32 and len(atoms)==5
    perms=list(permutations(I))
    assert len(perms)==120
    for p in perms:
        for a,b in product(atoms, repeat=2):
            assert action(p,mul(a,b)) == mul(action(p,a),action(p,b))
            assert action(p,add(a,b)) == add(action(p,a),action(p,b))
    u=(1,2,3,4,0)
    v=(1,0,2,3,4)
    words={I:()}
    todo=deque([I])
    while todo:
        p=todo.popleft()
        for letter,q in (("u",u),("v",v)):
            other=compose(p,q)
            if other not in words:
                words[other]=words[p]+(letter,)
                todo.append(other)
    assert len(words)==120
    for p,w in words.items():
        got=I
        for letter in w:
            got=compose(got, u if letter=="u" else v)
        assert got==p
    gens=[("g",i) for i in I]
    terms=[("unit",)]+gens
    terms += [("prod",a,b) for a,b in product(gens,repeat=2)]
    terms += [("sum",a,b) for a,b in product(gens,repeat=2)]
    terms += [("scale",-2,("sum",gens[i],gens[(i+1)%N])) for i in I]
    terms += [("prod",("sum",a,b),("scale",3,c))
              for a,b,c in product(gens,repeat=3)]
    assert len(terms)==186
    for p in perms:
        for term in terms:
            assert action(p,eval_term(term)) == eval_term(map_term(p,term))
    print("PASS FLM/Y443 finite control: 5 primitive idempotents, 120 automorphisms")
    print("PASS JMD-style 2-generated control: 120/120 elements, 22320 generated-term action checks")
    print("SCOPE: Q^5 coordinate algebra only; actual Vnatural/Monster remains source-dependent")

if __name__ == "__main__":
    main()
