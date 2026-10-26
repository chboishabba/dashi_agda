#!/usr/bin/env python3
"""Exact rational reference-branch audit, not PyTorch/GPU equivalence.
Original algorithm: Dahal, Mandal, Gülbahar, Vegesna; original dust.py blob
c7d08ee9edc3a51dfbd9e73bbf787b9ca819c5c2 (26 Oct 2026).
DASHI owns this independent finite branch discriminator.
"""
from fractions import Fraction as F
from itertools import product

def direct_rewards(clean, losses, nrep):
    assert nrep >= 1 and len(losses) == nrep
    rewards = [clean - p for p in losses]
    if nrep > 1:
        mean = sum(rewards, F(0))/nrep
        rewards = [r - mean for r in rewards]
    return rewards

def head_rewards(clean_by_batch, noisy_by_draw_batch):
    """Reflect upstream head_error condition if b>1, NOT if nrep>1.
    This finite analogue assumes all tokens valid and omits logits/slabs.
    """
    batch_size=len(clean_by_batch)
    rewards = [[clean_by_batch[b]-loss[b] for b in range(batch_size)]
               for loss in noisy_by_draw_batch]
    if batch_size>1:
        rewards=[[r-sum(row,F(0))/batch_size for r in row] for row in rewards]
    return rewards

def main():
    for clean, a, b in product((F(-3),F(0),F(7,2)), repeat=3):
        one=direct_rewards(clean,[a],1)
        two=direct_rewards(clean,[a,b],2)
        assert one==[clean-a]
        assert two==[(b-a)/2,(a-b)/2]
        assert sum(two)==0
    # nrep=2 and batch=1: direct centers, head does not.
    assert direct_rewards(F(10),[F(2),F(6)],2)==[F(2),F(-2)]
    assert head_rewards([F(10)],[[F(2)],[F(6)]])==[[F(8)],[F(4)]]
    # nrep=1 and batch=2: head centers, direct does not.
    assert direct_rewards(F(10),[F(2)],1)==[F(8)]
    assert head_rewards([F(10),F(10)],[[F(2),F(6)]])==[[F(2),F(-2)]]
    print('PASS: 27 exact rational direct-branch triples; 2 crossed head/direct centering discriminators')

if __name__=='__main__': main()
