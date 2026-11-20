from itertools import product
from collections import Counter
from math import comb
import sympy as s
for n in (2,3,6,9):
    c=Counter(tuple(abs(t) for t in x) for x in product((-1,0,1),repeat=n))
    assert len(c)==2**n and all(v==2**sum(k) for k,v in c.items())
    assert sum(c.values())==sum(comb(n,k)*2**k for k in range(n+1))==3**n
    print(n,len(c),sum(c.values()))
r=s.Matrix([[0,0,1],[1,0,0],[0,1,0]])
j=s.Matrix([[0,0,1],[0,1,0],[1,0,0]])
I=s.eye(3); P=(I+j)/2; N=(I-j)/2
assert j*r*j==r**2 and P*r*N!=s.zeros(3) and N*r*P!=s.zeros(3)
print('off-diagonal ranks', (P*r*N).rank(),(N*r*P).rank())
print('PASS')
