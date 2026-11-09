#!/usr/bin/env python3
"""Exact F2 abelianization check for literal DASHI Y443 79/80 relators.

Source transcription: Y443CoxeterPresentationExact.agda, Bray/Ivanov.
11 adjacent Coxeter pairs have exponent three, 55 nonadjacent exponent
two; 12 involution squares, spider word^10 and central word^9.
This proves the 79 presentation has two F2 characters, but the 80
presentation has only the trivial F2 character. This does NOT prove
the Monster presentation theorem or selected-group kernel reflection.
"""
from itertools import combinations

NODES="a b1 c1 d1 e1 b2 c2 d2 e2 b3 c3 d3".split()
EDGES=[("a","b1"),("b1","c1"),("c1","d1"),("d1","e1"),
       ("a","b2"),("b2","c2"),("c2","d2"),("d2","e2"),
       ("a","b3"),("b3","c3"),("c3","d3")]
INDEX={n:i for i,n in enumerate(NODES)}
SPIDER="a b1 c1 a b2 c2 a b3 c3".split()*10
CENTRAL="a b3 c3 d3 b1 c1 b2".split()*9

def mask(word):
    value=0
    for n in word:value^=1<<INDEX[n]
    return value

def rank(rows):
    basis={}
    for row in rows:
        while row:
            pivot=row.bit_length()-1
            if pivot not in basis:
                basis[pivot]=row
                break
            row^=basis[pivot]
    return len(basis)

def character_vanishes(bits,rows):
    return all((bits & row).bit_count()%2==0 for row in rows)

def main():
    pairs=list(combinations(NODES,2))
    edges=set(tuple(sorted(p)) for p in EDGES)
    assert len(pairs)==66 and len(edges)==11
    squares=[[n,n] for n in NODES]
    coxeter=[list(p)*(3 if tuple(sorted(p)) in edges else 2) for p in pairs]
    r79=squares+coxeter+[SPIDER]
    r80=r79+[CENTRAL]
    assert (len(r79),len(r80))==(79,80)
    assert (sum(map(len,r79)),sum(map(len,r80)))==(400,463)
    b79=list(map(mask,r79));b80=list(map(mask,r80))
    assert mask(SPIDER)==0
    assert rank(b79)==11 and rank(b80)==12
    chars79=[i for i in range(1<<12) if character_vanishes(i,b79)]
    chars80=[i for i in range(1<<12) if character_vanishes(i,b80)]
    assert chars79==[0,(1<<12)-1] and chars80==[0]
    print("PASS: Y443 original relator counts 79/80 and word lengths 400/463")
    print("PASS: original F2 parity ranks 11 (79) and 12 (80)")
    print("PASS: 79 relators admit exactly two mod-2 characters; 80 only trivial")
    print("SCOPE: abelian character test only; Monster and selected kernel OPEN")
if __name__=="__main__":main()
