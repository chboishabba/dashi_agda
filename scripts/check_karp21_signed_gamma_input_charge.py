#!/usr/bin/env python3
"""Source-grammar differential: native gamma signed token and entire signed raw edge stream charge <= original input bits."""
from itertools import product
from random import Random

def gamma_scan(bits):
    zeros=0
    while zeros<len(bits) and not bits[zeros]: zeros+=1
    if zeros>=len(bits) or len(bits)<2*zeros+1: return None
    return bits[zeros:2*zeros+1],bits[2*zeros+1:]

def unsigned_endpoint(bits):
    parsed=gamma_scan(bits)
    if parsed is None:return None
    return parsed[1]

def signed_gamma(bits):
    parsed=gamma_scan(bits)
    if parsed is None:return None
    successor,suffix=parsed
    magnitude,sign=successor[:-1],successor[-1]
    assert (len(magnitude)+1) + len(suffix) <= len(bits)
    return (tuple(magnitude),sign), suffix

def gamma(n):
    numeral=tuple(c=='1' for c in bin(n+1)[2:])
    return (False,)*(len(numeral)-1)+numeral

def signed_zigzag(w):return 2*w if w>=0 else -2*w-1

def raw_edges(count,bits):
    original=bits;total=0
    for _ in range(count):
        afterU=unsigned_endpoint(bits)
        if afterU is None:return None
        afterV=unsigned_endpoint(afterU)
        if afterV is None:return None
        read=signed_gamma(afterV)
        if read is None:return None
        (magnitude,sign),bits=read
        total+=1+len(magnitude)
        assert total+len(bits)<=len(original)
    return total,bits

def raw_all_fields(count,bits):
    original=bits;field_bits=0
    for _ in range(count):
        u=gamma_scan(bits)
        if u is None:return None
        successor_u,after_u=u
        v=gamma_scan(after_u)
        if v is None:return None
        successor_v,after_v=v
        signed=signed_gamma(after_v)
        if signed is None:return None
        (magnitude,sign),bits=signed
        field_bits += len(successor_u)+len(successor_v)+1+len(magnitude)
        assert field_bits+len(bits)<=len(original)
    return field_bits,bits

def main():
    cases=0;whole=0
    for n in range(15):
        for bits in product((False,True),repeat=n):
            signed_gamma(bits)
            for m in range(4):raw_edges(m,bits);raw_all_fields(m,bits);whole+=1
            cases+=1
    rng=Random(1972)
    for _ in range(20000):
        fields=[(rng.randrange(1<<rng.randrange(100)),rng.randrange(1<<rng.randrange(100)),rng.randrange(-(1<<60),1<<60)) for _ in range(rng.randrange(12))]
        word=tuple(bit for u,v,w in fields for bit in (gamma(u)+gamma(v)+gamma(signed_zigzag(w))))
        suffix=tuple(bool(rng.getrandbits(1)) for _ in range(rng.randrange(30)))
        result=raw_edges(len(fields),word+suffix)
        all_fields=raw_all_fields(len(fields),word+suffix)
        assert all_fields is not None and all_fields[1]==suffix and all_fields[0]+len(suffix)<=len(word+suffix)
        assert result is not None and result[1]==suffix
        assert result[0]+len(suffix)<=len(word+suffix)
        whole+=1
    print(f'Actual signed gamma token input-charge checks: {cases:,}/{cases:,} PASS')
    print(f'Actual signed raw-edge stream charge/suffix checks: {whole:,}/{whole:,} PASS')
    print(f'All original binary u/v/w register charges bounded by source input: {whole:,}/{whole:,} PASS')
if __name__=='__main__':main()
