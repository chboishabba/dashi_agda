#!/usr/bin/env python3
"""Same-state F2.2 N21 binary first-enabled live *payload* monotonicity.

Counts precisely: chronological history vertex bits + Bool labels,
remaining parsed edge u/v/sign/magnitude bits, remaining certificate,
and real two-lane ripple signed-ledger registers. Does NOT count
threshold/header, list cons/pointers, sharing/copies, stack or tape
head movement. Differential over actual source transition structure;
not Agda kernel checking or a physical bit-TM clock.
"""
from random import Random

def bits(n, padding=0):
    return tuple(bool((n >> i) & 1) for i in range(n.bit_length()+padding))

def val(word):
    return sum(int(b) << i for i,b in enumerate(word))

def add(a,b):
    carry=0;out=[]
    for i in range(max(len(a),len(b))):
        total=(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)+carry
        out.append(bool(total&1));carry=total>>1
    if carry:out.append(True)
    return tuple(out)

def signed_token(w):
    magnitude=abs(w)
    return w>=0, tuple(bool((magnitude >> i)&1)
                       for i in reversed(range(magnitude.bit_length())))

def capacity(edges,certificate,history,pos,neg):
    return (sum(1+len(vertex) for vertex,label in history)
            +sum(len(u)+len(v)+1+len(tok[1]) for u,v,tok in edges)
            +len(certificate)+len(pos)+len(neg))

def step(edges,certificate,history,pos,neg):
    if not edges:
        return edges,certificate,history,pos,neg,'finish' if not certificate else 'reject'
    if len(certificate)<2:
        return edges,certificate,history,pos,neg,'reject'
    u,v,token=edges[0];a,b=certificate[:2]
    if any(val(u)==val(x) and a!=label for x,label in history):
        return edges,certificate,history,pos,neg,'reject'
    if any(val(v)==val(x) and b!=label for x,label in history):
        return edges,certificate,history,pos,neg,'reject'
    if a!=b:
        positive,magnitude_be=token
        magnitude_le=tuple(reversed(magnitude_be))
        if positive: pos=add(pos,magnitude_le)
        else: neg=add(neg,magnitude_le)
    return edges[1:],certificate[2:],((u,a),(v,b))+history,pos,neg,'advance'

def main():
    rng=Random(1972);checks=0;advances=0;halts=0;peak=0
    for _ in range(30000):
        m=rng.randrange(13)
        edges=tuple((bits(rng.randrange(64),rng.randrange(3)),
                     bits(rng.randrange(64),rng.randrange(3)),
                     signed_token(rng.randrange(-(1<<25),1<<25)))
                    for _ in range(m))
        certificate=tuple(bool(rng.getrandbits(1))
                          for _ in range(rng.randrange(2*m+4)))
        history=tuple((bits(rng.randrange(64),rng.randrange(3)),
                       bool(rng.getrandbits(1)))
                      for _ in range(rng.randrange(9)))
        pos=bits(rng.randrange(1<<15),rng.randrange(2))
        neg=bits(rng.randrange(1<<15),rng.randrange(2))
        before=capacity(edges,certificate,history,pos,neg)
        for _ in range(m+1):
            new_edges,new_cert,new_history,new_pos,new_neg,action=step(
                edges,certificate,history,pos,neg)
            after=capacity(new_edges,new_cert,new_history,new_pos,new_neg)
            assert after<=before,(before,after,action)
            checks+=1;peak=max(peak,before,after)
            if action!='advance':
                halts+=1
                break
            advances+=1
            edges,certificate,history,pos,neg=(
                new_edges,new_cert,new_history,new_pos,new_neg)
            before=after
        else:
            raise AssertionError('actual binary first-enabled m+1 transition cap')
    print(f'Original N21 actual binary live payload monotonic transitions: {checks:,}/{checks:,} PASS')
    print(f'Advances: {advances:,}; terminal/rejects: {halts:,}; largest payload: {peak:,} bits')
    print('Only counted source data fields; not Agda, physical list allocations, or bit-TM clock.')

if __name__=='__main__':main()
