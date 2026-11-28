#!/usr/bin/env python3
"""Actual #1548 threshold-clamp bit clock, binary streaming without expansion.

The Agda theorem PNPAggregateGateCountExact.boundedDecode/Encode already
proves semantics for unary Nat cap. This supplies a deterministic streaming
binary reference algorithm plus an exact inductive proof obligation to weld
the original binary-encoded k to that Nat, retaining the REAL bit clock.
This is NOT an NP lower bound or a universal polynomial SAT algorithm.
"""
from itertools import product

def saturated_binary(bits, maximum):
    assert maximum >= 0
    accumulator = 0
    for bit in bits:
        assert bit in '01'
        accumulator = min(maximum, accumulator*2+(bit == '1'))
    return accumulator

def capacity(rows):
    return sum(max(0, length-target) for length,target in rows)

def proof_step(maximum, x, b):
    """min(M,2 min(M,x)+b) = min(M,2x+b) for M,x>=0,b in {0,1}."""
    return min(maximum,2*min(maximum,x)+b)==min(maximum,2*x+b)

def main():
    total=0
    for m in range(0,17):
        for x in range(0,90):
            for b in (0,1):
                assert proof_step(m,x,b)
                total+=1
    for length in range(0,11):
        for bs in product('01',repeat=length):
            bits=''.join(bs)
            for m in (0,1,2,3,11,1024):
                assert saturated_binary(bits,m)==min(m,int(bits or '0',2))
                total+=1
    # No huge integer construction; bounded state after every consumed bit.
    huge='10110001'*16384
    assert saturated_binary(huge,7)==7
    rows=((3,2),(5,0),(8,5))
    assert capacity(rows)==9
    assert saturated_binary(huge,capacity(rows))==9
    print('PASS',total,'inductive step/bit-prefix instances and 131072-bit stream')

if __name__=='__main__':
    main()
