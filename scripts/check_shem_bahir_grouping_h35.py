from sympy import Matrix, GF, __version__
from sympy.polys.matrices import DomainMatrix
from itertools import product
from math import log2

indices=list(product(range(3),range(4),range(6)))
assert [24*g+6*h+k for g,h,k in indices]==list(range(72))
rows=[]
for g in range(3): rows.append([int(a==g) for a,b,c in indices])
for g,h in product(range(3),range(4)): rows.append([int((a,b)==(g,h)) for a,b,c in indices])
for h in range(4): rows.append([int(b==h) for a,b,c in indices])
for k in range(6): rows.append([int(c==k) for a,b,c in indices])
def rank(rows):
    return DomainMatrix.from_Matrix(Matrix(rows)).convert_to(GF(3)).rank()
assert rank(rows)==17
anchors=[[int(j==i) for j in range(72)] for i in [0,36]]
assert rank(rows+anchors)==19
# Even if every marginal is given, a local signed rectangle perturbation
# in one six-by-six? no: one group, two directions, two slots preserves all marginals.
delta=[0]*72
for h,k,s in [(1,1,1),(1,2,-1),(2,1,-1),(2,2,1)]: delta[24*0+6*h+k]=s
assert any(delta) and all(v%3==0 for v in Matrix(rows+anchors)*Matrix(delta))
print('SymPy',__version__,'ranks',rank(rows),rank(rows+anchors),'oracle bits',55*log2(27),53*log2(27),'nonzero rectangle kernel PASS')
