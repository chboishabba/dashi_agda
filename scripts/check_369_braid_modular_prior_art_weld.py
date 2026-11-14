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


# Exact native Z/2 orbifold sector action:
# S(g,h)=(h,g), T_orb(g,h)=(g,g+h) over F2.
sectors=[(g,h) for g in (0,1) for h in (0,1)]
S=lambda z:(z[1],z[0])
Torb=lambda z:(z[0],z[0]^z[1])
sigma1=lambda z:S(Torb(S(z)))
sigma2=Torb
for z in sectors:
    assert sigma1(sigma2(sigma1(z)))==sigma2(sigma1(sigma2(z)))
    assert sigma2(sigma1(z))==S(Torb(z))
    assert sigma1(sigma1(z))==sigma2(sigma2(z))==z
    pure=z
    for _ in range(3):pure=sigma1(sigma2(pure))
    assert pure==z
roles={'thesis':(0,1),'mediating':(1,1),'antithesis':(1,0)}
role_sigma1={'thesis':'mediating','mediating':'thesis','antithesis':'antithesis'}
role_sigma2={'thesis':'thesis','mediating':'antithesis','antithesis':'mediating'}
for name,z in roles.items():
    assert roles[role_sigma1[name]]==sigma1(z)
    assert roles[role_sigma2[name]]==sigma2(z)
    assert roles[role_sigma2[role_sigma1[name]]]==S(Torb(z))

# Existing OggSSPP2BalancedTernaryPuncturedPlaneExact punctured T9.
nonzero={(x,y) for x in (-1,0,1) for y in (-1,0,1)}-{(0,0)}
residue=lambda v:{0:0,1:1,2:-1}[v%3]
act=lambda z:(residue(13*z[0]-8*z[1]),residue(-8*z[0]+5*z[1]))
antipode=lambda z:(-z[0],-z[1])
assert {act(p) for p in nonzero}==nonzero
assert all(act(act(p))==antipode(p) and act(act(act(act(p))))==p for p in nonzero)
assert all(act(p)!=p for p in nonzero)
cycles=[];remaining=set(nonzero)
while remaining:
    start=min(remaining);cur=start;cycle=[]
    while cur not in cycle:
        cycle.append(cur);remaining.remove(cur);cur=act(cur)
    assert cur==start
    cycles.append(cycle)
assert sorted(map(len,cycles))==[4,4],cycles
print('PASS B3->SL2(F2) matches native twisted Z/2 orbifold S/T sector action')
print('PASS C3 strand roles equivariantly match three nontrivial orbifold sectors')
print('PASS pure braid is invisible mod2, but acts as 2x4-cycles on punctured T9 mod3:',cycles)
