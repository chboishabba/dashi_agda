#!/usr/bin/env python3
"""Same-source binary graph + selected-sign-event + ripple ledger width check.
Finite executable differential, never an Agda kernel or Turing clock receipt.
"""
from random import Random
from itertools import combinations, product
from check_karp21_signed_gamma_input_charge import gamma, signed_gamma, unsigned_endpoint

def bits_le(n):
    return tuple(bool((n >> i) & 1) for i in range(n.bit_length()))

def ripple_add(a,b):
    carry=0; result=[]
    for i in range(max(len(a),len(b))):
        s=(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)+carry
        result.append(bool(s&1));carry=s>>1
    if carry:result.append(True)
    return tuple(result)

def zigzag(w):return 2*w if w>=0 else -2*w-1

def parse_graph_and_charge(word):
    nread=unsigned_endpoint(word)
    if nread is None:return None
    mread=unsigned_endpoint(nread)
    if mread is None:return None
    _, after_n = (None, nread)
    header_len=len(word)-len(mread)
    return mread,header_len

def run_case(n,edges,labels,threshold):
    original=gamma(n)+gamma(len(edges))
    for u,v,w in edges:
        original+=gamma(u)+gamma(v)+gamma(zigzag(w))
    original+=gamma(threshold)
    after_n=unsigned_endpoint(original)
    assert after_n is not None
    after_m=unsigned_endpoint(after_n)
    assert after_m is not None
    cursor=after_m; tokens=[]; total_charge=0
    for u,v,w in edges:
        after_u=unsigned_endpoint(cursor); assert after_u is not None
        after_v=unsigned_endpoint(after_u); assert after_v is not None
        parsed=signed_gamma(after_v);assert parsed is not None
        token,cursor=parsed
        total_charge+=1+len(token[0]);tokens.append(token)
        assert total_charge+len(cursor)<=len(after_m)
    assert total_charge+len(cursor)<=len(after_m)<=len(original)
    pos=neg=()
    selected_charge=0
    for (u,v,w),token in zip(edges,tokens):
        if labels[u]!=labels[v]:
            magnitude_be,sign=token
            signed_charge=1+len(magnitude_be)
            selected_charge+=signed_charge
            if sign:pos=ripple_add(pos,tuple(reversed(magnitude_be)))
            else:neg=ripple_add(neg,tuple(reversed(magnitude_be)))
            assert len(pos)+len(neg)<=selected_charge
    assert selected_charge<=total_charge
    assert len(pos)+len(neg)<=len(original)
    return len(original),selected_charge,len(pos)+len(neg)

def main():
    cases=0;below=0;max_width=0
    for n in range(5):
        pairs=[(u,v) for u in range(n) for v in range(u+1,n)]
        for size in range(min(len(pairs),3)+1):
            for chosen in combinations(pairs,size):
                for ws in product((-3,0,5),repeat=size):
                    edges=[(u,v,w) for (u,v),w in zip(chosen,ws)]
                    for labels in product((False,True),repeat=n):
                        original,charge,width=run_case(n,edges,labels,1)
                        cases+=1;max_width=max(max_width,width)
    rng=Random(1972)
    for _ in range(30000):
        n=rng.randrange(2,24)
        pairs=[(u,v) for u in range(n) for v in range(u+1,n)]
        chosen=sorted(rng.sample(pairs,rng.randrange(min(len(pairs),12)+1)))
        edges=[(u,v,rng.randrange(-(1<<70),1<<70)) for u,v in chosen]
        labels=tuple(bool(rng.getrandbits(1)) for _ in range(n))
        threshold=rng.randrange(1,1<<80)
        original,charge,width=run_case(n,edges,labels,threshold)
        cases+=1;max_width=max(max_width,width)
        if sum(w for u,v,w in edges if labels[u]!=labels[v])<threshold:
            below+=1
    print(f'Actual original graph -> selected signed-token -> two-lane width checks: {cases:,}/{cases:,} PASS')
    print(f'Below-threshold valid traces also costed: {below:,}; max final register width: {max_width}')
    print('Finite source-grammar model only: no Agda kernel or physical tape cost receipt.')
if __name__=='__main__':main()
