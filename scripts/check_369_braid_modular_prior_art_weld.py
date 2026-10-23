#!/usr/bin/env python3
"""Exact generator audit, B3->SL2(Z), and full 3/9/27 modular residues.
This tests a prior recorded braid word, not an analytic VOA/KK equivalence.
"""
I=((1,0),(0,1))
T=((1,1),(0,1))
L=((1,0),(1,1))  # EXISTING signed-SSP lower shear; not Artin sigma2
U=((1,0),(-1,1)) # Correct Artin sigma2 = L inverse
Ti=((1,-1),(0,1))

def mul(A,B):
    return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)) for i in range(2))
def powmat(A,n):
    z=I
    while n:
        if n&1:z=mul(z,A)
        A=mul(A,A);n//=2
    return z
def mod(A,n):
    return tuple(tuple(z%n for z in row) for row in A)
def order(A,n,cap=20000):
    a=I
    for i in range(1,cap):
        a=mod(mul(a,A),n)
        if a==I:return i
    raise AssertionError(f'no order detected modulo {n}')

assert mul(T,U)==((0,1),(-1,1))
assert mul(mul(T,U),T)==mul(mul(U,T),U)
assert mul(L,U)==mul(U,L)==I
assert mul(mul(T,L),T)!=mul(mul(L,T),L)
C=powmat(mul(T,U),3)
assert C==((-1,0),(0,-1))
assert powmat(mul(T,U),6)==I
V=mul(Ti,U)
M=powmat(V,3)
assert M==((13,-8),(-8,5)),M
assert 13*5-(-8)*(-8)==1
assert sum(M[i][i] for i in range(2))==18
expected={3:4,9:4,27:12}
for n,o in expected.items():
    assert order(M,n)==o,(n,order(M,n))
    assert mod(powmat(M,o),n)==I
    assert mod(powmat(M,o//2),n)==mod(C,n)
assert all(mod(M,n)!=I for n in expected)
assert mod(M,3)==((1,1),(1,2))
assert mod(M,9)==((4,1),(1,5))
assert mod(M,27)==((13,19),(19,5))
print('PASS prior-art positive lower shear L is inverse to braid sigma2 U; TLT != LTL')
print('PASS B3 relation and central full twist -> -I; modular word ->',M)
print('PASS finite orders mod (3,9,27):', expected)
print('PASS half-order -> -I at all three principal levels')
print('RESIDUAL actual geometric braid lift, VOA modular multipliers, physical AdS3 and KK action')
