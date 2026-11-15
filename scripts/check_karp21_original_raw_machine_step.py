#!/usr/bin/env python3
"""Original paired-raw-list source step vs actual binary endpoint step.

Compare full NONTERMINAL next states after observing binary u/v and
chronological history as Nat. For terminals, old raw-list finished
is composed with positive W, not falsely identified with the new
whole binary accepted/rejected phase. Finite test only: no Agda proof.
"""
from itertools import product
from random import Random
from check_karp21_whole_binary_graph import compare_le, val

def le(n, padding=0):
    return tuple(bool((n >> i) & 1) for i in range(n.bit_length()+padding))

def binary_step(edges, cert, hist, pos, neg, threshold):
    if not edges:
        if cert:
            return ('rejected',edges,cert,hist,pos,neg)
        return ('accepted' if pos-neg>=val(threshold) else 'rejected',
                edges,cert,hist,pos,neg)
    if len(cert)<2:
        return ('rejected',edges,cert,hist,pos,neg)
    u,v,weight=edges[0]
    a,b=cert[:2]
    if any(compare_le(u,x)==0 and a!=observed for x,observed in hist):
        return ('rejected',edges,cert,hist,pos,neg)
    if any(compare_le(v,x)==0 and b!=observed for x,observed in hist):
        return ('rejected',edges,cert,hist,pos,neg)
    if a!=b:
        if weight>=0:pos+=weight
        else:neg+=-weight
    return ('active',edges[1:],cert[2:],((u,a),(v,b))+hist,pos,neg)

def original_step(edges,cert,hist,pos,neg):
    if not edges:
        if cert:
            return ('rejected',edges,cert,hist,pos,neg)
        return ('finished',edges,cert,hist,pos,neg)
    if len(cert)<2:
        return ('rejected',edges,cert,hist,pos,neg)
    u,v,weight=edges[0]
    a,b=cert[:2]
    if any(x==u and a!=observed for x,observed in hist):
        return ('rejected',edges,cert,hist,pos,neg)
    if any(x==v and b!=observed for x,observed in hist):
        return ('rejected',edges,cert,hist,pos,neg)
    if a!=b:
        if weight>=0:pos+=weight
        else:neg+=-weight
    return ('active',edges[1:],cert[2:],((u,a),(v,b))+hist,pos,neg)

def observe(binary_state):
    phase,edges,cert,hist,pos,neg=binary_state
    return (phase,tuple((val(u),val(v),w) for u,v,w in edges),cert,
            tuple((val(x),bit) for x,bit in hist),pos,neg)

def check_nonterminal(edges,cert,hist,pos,neg,threshold):
    got=observe(binary_step(edges,cert,hist,pos,neg,threshold))
    observed_edges=tuple((val(u),val(v),w) for u,v,w in edges)
    observed_hist=tuple((val(x),bit) for x,bit in hist)
    want=original_step(observed_edges,cert,observed_hist,pos,neg)
    assert got==want,(edges,cert,hist,got,want)

def check_terminal(pos,neg,threshold):
    got=binary_step((),(),(),pos,neg,threshold)
    old=original_step((),(),(),pos,neg)
    assert old[0]=='finished'
    assert got[0]==('accepted' if pos-neg>=val(threshold) else 'rejected')
    if pos-neg<val(threshold):assert got[0]!=old[0]

def main():
    checked=0
    for u,v,w in product(range(3),range(3),(-3,0,2)):
        for a,b in product((False,True),repeat=2):
            for width in range(4):
                for cert in product((False,True),repeat=width):
                    edge=((le(u,a),le(v,b),w),)
                    hist=((le(u,not a),True),(le(v,not b),False))
                    check_nonterminal(edge,cert,hist,0,0,le(1))
                    checked+=1
    rng=Random(1972)
    for _ in range(25000):
        edges=tuple((le(rng.randrange(7),rng.randrange(4)),
                     le(rng.randrange(7),rng.randrange(4)),
                     rng.randrange(-(1<<32),1<<32))
                    for _ in range(rng.randrange(1,9)))
        cert=tuple(bool(rng.getrandbits(1)) for _ in range(rng.randrange(20)))
        hist=tuple((le(rng.randrange(7),rng.randrange(4)),
                    bool(rng.getrandbits(1))) for _ in range(rng.randrange(15)))
        check_nonterminal(edges,cert,hist,rng.randrange(1000),rng.randrange(1000),
                          le(rng.randrange(1,100)))
        checked+=1
    terminal=0
    for pos in range(9):
        for neg in range(9):
            for threshold in range(1,12):
                check_terminal(pos,neg,le(threshold))
                terminal+=1
    print(f'Original raw-list vs bit-native nonterminal state: {checked:,}/{checked:,} PASS')
    print(f'Old raw-finished + W vs binary fused terminal: {terminal:,}/{terminal:,} PASS')
    print('Finite regression only; does not certify Agda or physical TM.')

if __name__=='__main__':main()
