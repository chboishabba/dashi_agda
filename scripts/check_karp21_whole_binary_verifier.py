#!/usr/bin/env python3
"""Original signed N21 Fin-free verifier versus actual bit-register pipeline.

Finite differential only; not Agda kernel/typecheck or a physical tape clock.
"""
from itertools import product
from random import Random
from check_karp21_binary_header_budget import (
    gamma, gamma_scan, native_unsigned, original_header, ripple_add,
    length_le, compare_le, val, predecessor_le
)

def signed_bits(bits):
    parsed=gamma_scan(bits)
    if parsed is None:return None
    numeral,rest=parsed
    n=0
    for b in numeral:n=2*n+int(b)
    n-=1
    return (n//2 if n%2==0 else -(n//2+1)),rest

def edges_original(m,word):
    edges=[]
    for _ in range(m):
        a=gamma_scan(word)
        if a is None:return None
        num,word=a;u=0
        for b in num:u=2*u+int(b)
        u-=1
        a=gamma_scan(word)
        if a is None:return None
        num,word=a;v=0
        for b in num:v=2*v+int(b)
        v-=1
        a=signed_bits(word)
        if a is None:return None
        w,word=a
        edges.append((u,v,w))
    return edges,word

def original_graph(word):
    header=original_header(word,True)
    if header is None:return None
    n,m,word=header
    parsed=edges_original(m,word)
    if parsed is None:return None
    edges,word=parsed
    final=gamma_scan(word)
    if final is None:return None
    numeral,rest=final
    threshold=0
    for b in numeral:threshold=2*threshold+int(b)
    threshold-=1
    if rest or threshold<=0:return None
    prev=None
    for u,v,_ in edges:
        if not(u<v<n and (prev is None or (u,v)>prev)):return None
        prev=(u,v)
    return edges,threshold

def original_decision(word,cert):
    parsed=original_graph(word)
    if parsed is None:return False
    edges,threshold=parsed
    if len(cert)!=2*len(edges):return False
    hist=[];score=0
    for i,(u,v,w) in enumerate(edges):
        a,b=cert[2*i:2*i+2]
        if any(x==u and a!=t for x,t in hist):return False
        if any(x==v and b!=t for x,t in hist):return False
        hist=[(u,a),(v,b)]+hist
        if a!=b:score+=w
    return score>=threshold

def binary_decision(word,cert):
    a=native_unsigned(word)
    if a is None:return False
    n,word=a
    a=native_unsigned(word)
    if a is None:return False
    m,word=a
    if compare_le(length_le(word),ripple_add(m,ripple_add(m,m)))<0:return False
    edges=[];fuel=len(word)
    while val(m):
        if fuel==0:return False
        fuel-=1
        a=native_unsigned(word)
        if a is None:return False
        u,word=a
        a=native_unsigned(word)
        if a is None:return False
        v,word=a
        a=signed_bits(word)
        if a is None:return False
        w,word=a
        edges.append((u,v,w))
        m=predecessor_le(m)
    a=native_unsigned(word)
    if a is None:return False
    threshold,word=a
    if val(threshold)==0 or word:return False
    prev=None
    for u,v,_ in edges:
        if compare_le(u,v)>=0 or compare_le(v,n)>=0:return False
        if prev is not None:
            x,y=prev
            if not(compare_le(x,u)<0 or (compare_le(x,u)==0 and compare_le(y,v)<0)):
                return False
        prev=u,v
    if len(cert)!=2*len(edges):return False
    hist=[];pos=neg=()
    for i,(u,v,w) in enumerate(edges):
        a,b=cert[2*i:2*i+2]
        if any(compare_le(u,x)==0 and a!=t for x,t in hist):return False
        if any(compare_le(v,x)==0 and b!=t for x,t in hist):return False
        hist=[(u,a),(v,b)]+hist
        if a!=b:
            k=abs(w)
            bits=tuple(bool((k>>j)&1) for j in range(k.bit_length()))
            if w>=0:pos=ripple_add(pos,bits)
            else:neg=ripple_add(neg,bits)
    return compare_le(pos,ripple_add(neg,threshold))>=0

def main():
    checks=0
    for size in range(15):
        for word in product((False,True),repeat=size):
            for cert in ((),(False,),(True,False),(True,False,True)):
                assert binary_decision(word,cert)==original_decision(word,cert)
                checks+=1
    rng=Random(1972)
    for _ in range(900):
        n=rng.randrange(30)
        all_edges=[(u,v) for u in range(n) for v in range(u+1,n)]
        selected=sorted(rng.sample(all_edges,min(rng.randrange(11),len(all_edges))))
        triples=[(u,v,rng.randrange(-2**32,2**32)) for u,v in selected]
        word=gamma(n)+gamma(len(triples))
        for u,v,w in triples:
            zz=2*w if w>=0 else -2*w-1
            word+=gamma(u)+gamma(v)+gamma(zz)
        word+=gamma(rng.randrange(1,2**16))
        for _ in range(4):
            cert=tuple(bool(rng.getrandbits(1)) for _ in range(rng.randrange(2*len(triples)+4)))
            assert binary_decision(word,cert)==original_decision(word,cert)
            checks+=1
    print(f'Original N21 signed verifier vs whole binary pipeline: {checks:,}/{checks:,} PASS')

if __name__=="__main__":main()
