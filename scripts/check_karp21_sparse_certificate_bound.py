#!/usr/bin/env python3
"""G2 actual original N21 accepted sparse certificate bound regression.

Checks the real repository binary_decision program; deliberately
constructs accepting signed maximum-cut witnesses, plus invalid
and truncated certificates, and checks exactly 2 source cut bits
per parsed edge and <= original graph input bits, via the original 3m guard. Not Agda proof.
"""
from random import Random
from check_karp21_binary_header_budget import gamma
from check_karp21_whole_binary_verifier import binary_decision, original_graph

def main():
    rng=Random(2026)
    valid_accepts=0;rejected_checks=0
    for _ in range(7500):
        n=rng.randrange(2,48)
        pairs=[(u,v) for u in range(n) for v in range(u+1,n)]
        chosen=sorted(rng.sample(pairs,rng.randrange(1,min(12,len(pairs))+1)))
        labels=tuple(bool(rng.getrandbits(1)) for _ in range(n))
        weights=tuple(rng.randrange(1,1<<20) for _ in chosen)
        score=sum(w for (u,v),w in zip(chosen,weights)
                  if labels[u]!=labels[v])
        threshold=score if score>0 else 1
        word=gamma(n)+gamma(len(chosen))
        for (u,v),w in zip(chosen,weights):
            word+=gamma(u)+gamma(v)+gamma(2*w)
        word+=gamma(threshold)
        cert=tuple(bit for u,v in chosen for bit in (labels[u],labels[v]))
        parsed=original_graph(word)
        assert parsed is not None and len(parsed[0])==len(chosen)
        assert len(cert)==len(chosen)+len(chosen)
        assert 2*len(chosen)<=len(word)
        if score>0:
            assert binary_decision(word,cert),('expected accepted',len(word))
            assert len(cert)<=len(word)
            valid_accepts+=1
        else:
            assert not binary_decision(word,cert)
            rejected_checks+=1
        # A fully consumed original sparse certificate cannot leave
        # one extra label bit or lack one of the original 2m bits.
        assert not binary_decision(word,cert+(True,))
        assert not binary_decision(word,cert[:-1])
        rejected_checks+=2
    assert valid_accepts>4000,(valid_accepts,rejected_checks)
    print(f'Actual signed N21 accepted sparse certificate bounds: {valid_accepts:,}/{valid_accepts:,} PASS')
    print(f'Original below-threshold/truncated/extra-certificate rejection: {rejected_checks:,}/{rejected_checks:,} PASS')
    print('Finite binary verifier test only; not Agda or actual bit-Turing time.')
if __name__=='__main__':main()
