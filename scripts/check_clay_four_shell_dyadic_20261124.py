"""Exact finite algebra/geometry regression, not PDE, cohomology or native proof."""
from itertools import product, permutations
from fractions import Fraction as Q
from math import prod
import sympy as S
# NS: use j multiples of three so R^(1/3), R^(2/3) integral.
count=0
for j in (3,6,9):
    R=2**j
    for L in (2**(j//3),2**(2*j//3)):
        assert L<=R//2
        for k in [(R,0,0),(2*R-1,0,0),(R,R,0),(R,R,R)]:
            for p in product((-L,0,L),repeat=3):
                if sum(v*v for v in p)>L*L: continue
                h=sum((x-y)**2 for x,y in zip(k,p))
                assert Q(R*R,4)<=h<=Q(25*R*R,4)
                count+=1
for r in range(1,2049):
    assert sum(Q(2**j,2)<=r<=Q(5*2**j,2) for j in range(3,14))<=3
print('NS shell geometry:',count,'annular overlap: 2048')
# BSD: abstract cyclic components for the actual restriction/norm composition law.
count=0
for n in range(1,9):
    m=2**n
    for x,y in product(range(m),repeat=2):
        a,b=(x+y)%m,(x-y)%m
        assert ((a+b)%m,(a-b)%m)==((2*x)%m,(2*y)%m)
        count+=1
    image={((x+y)%m,(x-y)%m) for x,y in product(range(m),repeat=2)}
    assert len(image)==m*m//2
    assert all(((2*x)%m,(2*y)%m) in image for x,y in product(range(m),repeat=2))
print('BSD integral composition:',count,'8 image/index checks')
# Hodge determinant pairing: alternating tensor normalisation and reflection.
count=0
for m in range(2,7):
    g=[Q((-1)**i*(i+1),i+2) for i in range(m)]
    ps=list(permutations(range(m)))
    sign=lambda p:(-1)**sum(p[i]>p[j] for i in range(m) for j in range(i+1,m))
    det=prod(g); fact=S.factorial(m)
    # Coefficient on the alternating volume tensor in projected coevaluation.
    for p in ps:
        # contraction along matched coordinate permutations removes the q-sign in one leg
        val=sum(Q(sign(p),int(fact)*int(fact))*prod(1/g[i] for i in q) for q in ps)
        assert val==Q(sign(p),int(fact))/det
        count+=1
    assert prod([-1]+[1]*(m-1))==-1
print('Hodge alternating coevaluation coefficients:',count)
