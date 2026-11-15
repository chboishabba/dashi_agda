#!/usr/bin/env python3
"""Exhaustive independent integer reference for Karp21BinaryNativeThresholdExact.

Compares arbitrary zero-padded little-endian binary integer words and
signed two-lane threshold results. This is a finite differential test,
NOT kernel acceptance or a proof of graph-level resource bounds.
"""
def bits(n):
    return [int(c) for c in bin(n)[2:]][::-1]

def add(a,b):
    result, carry = [], 0
    for i in range(max(len(a),len(b))):
        total = (a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)+carry
        result.append(total & 1)
        carry = total >> 1
    if carry: result.append(1)
    return result

def order_bit(a,b):
    return (a > b) - (a < b)

def compare_le(xs, ys):
    if not xs and not ys: return 0
    a, b = (xs[0] if xs else 0), (ys[0] if ys else 0)
    high = compare_le(xs[1:],ys[1:])
    return high if high else order_bit(a,b)

def meets(positive,negative,threshold):
    p, n = bits(positive),bits(negative)
    if threshold >= 0:
        return compare_le(p,add(n,bits(threshold)))>=0
    return compare_le(add(p,bits(-threshold)),n)>=0

def main():
    cases=0
    for p in range(96):
        for n in range(96):
            for threshold in range(-20,21):
                assert meets(p,n,threshold) == (p-n>=threshold)
                cases+=1
    assert cases==377856
    print(f"PASS {cases} two-lane signed threshold cases")

if __name__=="__main__":
    main()
