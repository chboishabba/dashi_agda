#!/usr/bin/env python3
"""Exact congruence-depth theorem for the recorded B3 -> SL2Z braid image.

M=(T^-1 U)^3=[[13,-8],[-8,5]].
For every k>=2, order(M mod 3^k)=4*3^(k-2); for k=1, order 4.
Proof: M mod 9 has order 4 and M^4 = I + 3^2 B with B not
divisible by 3 entrywise. For any matrix X=I+3^s C (s>=1,
C nonzero mod 3), binomial expansion X^3=I+3^(s+1)
(C+3^s C^2+3^(2s-1) C^3), preserving C mod 3; cubing
adds exactly 1 to the 3-adic valuation. Any exponent m prime to
3 preserves the initial valuation by the same binomial argument.
The group order then follows from the mod-9 order and valuations.
Neither this finite arithmetic nor the previous B3 word certificate
supplies an analytic Monster VOA or AdS3 bulk action.
"""
I=((1,0),(0,1))
M=((13,-8),(-8,5))

def mul(a,b,mod=None):
    v=tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2))
                  for j in range(2)) for i in range(2))
    if mod is None:return v
    return tuple(tuple(t%mod for t in row) for row in v)

def power(a,n,mod=None):
    q=I
    while n:
        if n&1:q=mul(q,a,mod)
        a=mul(a,a,mod);n//=2
    return q

def subtract(a,b):
    return tuple(tuple(a[i][j]-b[i][j] for j in range(2))
                 for i in range(2))

assert power(M,4)==((75025,-46368),(-46368,28657))
B=tuple(tuple(z//9 for z in row) for row in subtract(power(M,4),I))
assert B==((8336,-5152),(-5152,3184))
assert any(z%3 for row in B for z in row)
assert power(M,2,9)==((8,0),(0,8))
assert power(M,4,9)==I

for k in range(1,13):
    n=3**k
    order=4 if k==1 else 4*3**(k-2)
    assert power(M,order,n)==I,(k,order)
    assert power(M,order//2,n)!=I,(k,order)
    if order%3==0:assert power(M,order//3,n)!=I,(k,order)
    if k>1:
        assert power(M,order//2,n)==tuple(
            tuple(((-1 if i==j else 0)%n) for j in range(2))
            for i in range(2))
    if k>1:
        reduction=3**(k-1)
        assert tuple(tuple(x%reduction for x in row) for row in power(M,order,n))==I

# The same integral element is identity in the mod-2 sector observer,
# yet is nontrivial in every level 3^k.
assert power(M,1,2)==I
assert all(power(M,1,3**k)!=I for k in range(1,9))
print("PASS exact infinite-level order formula (binomial lifting premise and 12 levels)")
print("M^4=I+9B, B mod 3 nonzero:",B)
print("order(M mod 3^k)=4 for k=1, and 4*3^(k-2) for all k>=2")
print("coarse mod-2 twisted-sector action loses the nontrivial 3-adic monodromy")
