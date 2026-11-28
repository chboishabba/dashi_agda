from fractions import Fraction as F
import hashlib

def source_terms(n):
    z=t=F(0)
    for m in range(n+1):
        yield m,z,t
        z,t=z*F(1,2)+F(1,2)**m,t*F(1,2)+z

N=1024
triples=list(source_terms(2*N+1))
checks=0
budget=F(0)
for k in range(N):
    m=2*k+1
    qz,ts=triples[m][1:]
    assert qz==m*F(1,2)**(m-1)
    expect=F(m*(m-1),2)*F(1,2)**(m-2) if m>1 else F(0)
    assert ts==expect
    atom=ts/F(m)
    assert atom==F(2*k,4**k)
    budget+=atom
    assert budget==F(8,9)*(1-F(3*(k+1)+1,4**(k+1)))
    assert F(0)<=budget<=F(8,9)
    checks+=5
assert triples[3][2]==F(3,2)
assert triples[3][2]/3==F(1,2)
assert triples[3][2]/5 != F(1,2)
assert triples[3][2] != F(3,4)
print('PASS',checks,'exact rational recurrence/readback identities; 2 corrupt controls rejected; nmax',N)
