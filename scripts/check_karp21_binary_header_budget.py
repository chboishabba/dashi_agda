#!/usr/bin/env python3
"""Original gamma n,m plus original 3*m guard against bit-only source parser.
Finite independent differential, not a kernel proof or physical TM clock.
"""
from itertools import product
from random import Random

def gamma_scan(bits):
    k=0
    while k<len(bits) and not bits[k]: k+=1
    if k>=len(bits) or len(bits)<2*k+1:return None
    return bits[k:2*k+1],bits[2*k+1:]

def predecessor_le(bits):
    borrow=True;out=[]
    for bit in bits:
        if borrow:out.append(not bit);borrow=not bit
        else:out.append(bit)
    return tuple(out)

def native_unsigned(word):
    p=gamma_scan(word)
    if p is None:return None
    successor,suffix=p
    return predecessor_le(tuple(reversed(successor))),suffix

def val(bits):return sum(int(b)<<i for i,b in enumerate(bits))

def ripple_add(xs,ys):
    carry=0;out=[]
    for i in range(max(len(xs),len(ys))):
        s=(int(xs[i]) if i<len(xs) else 0)+(int(ys[i]) if i<len(ys) else 0)+carry
        out.append(bool(s&1));carry=s>>1
    if carry:out.append(True)
    return tuple(out)

def length_le(word):
    result=()
    for _ in word:result=ripple_add((True,),result)
    return result

def compare_le(xs,ys):
    result=0
    for i in range(max(len(xs),len(ys))):
        a=bool(xs[i]) if i<len(xs) else False
        b=bool(ys[i]) if i<len(ys) else False
        if a!=b:result=1 if a else -1
    return result

def binary_budget(m,word):
    triple=ripple_add(m,ripple_add(m,m))
    return compare_le(length_le(word),triple)>=0

def native_header(word,budget):
    first=native_unsigned(word)
    if first is None:return None
    n,after_n=first
    second=native_unsigned(after_n)
    if second is None:return None
    m,rest=second
    if budget and not binary_budget(m,rest):return None
    return val(n),val(m),rest

def original_header(word,budget):
    first=gamma_scan(word)
    if first is None:return None
    nbits,after_n=first
    second=gamma_scan(after_n)
    if second is None:return None
    mbits,rest=second
    n=m=0
    for b in nbits:n=2*n+int(b)
    for b in mbits:m=2*m+int(b)
    n-=1;m-=1
    if budget and 3*m>len(rest):return None
    return n,m,rest

def gamma(n):
    bits=tuple(bool(int(c)) for c in bin(n+1)[2:])
    return (False,)*(len(bits)-1)+bits

def main():
    count=0
    for size in range(16):
        for word in product((False,True),repeat=size):
            for budget in (False,True):
                assert native_header(word,budget)==original_header(word,budget)
                count+=1
    rng=Random(1972)
    for _ in range(8000):
        n=rng.randrange(1<<rng.randrange(300))
        m=rng.randrange(1<<rng.randrange(300))
        rest=tuple(bool(rng.getrandbits(1)) for _ in range(rng.randrange(280)))
        word=gamma(n)+gamma(m)+rest
        for budget in (False,True):
            assert native_header(word,budget)==original_header(word,budget)
            count+=1
    print(f'Original n/m headers + 3m guard vs native LE binary implementation: {count:,} PASS')

if __name__=='__main__':main()
