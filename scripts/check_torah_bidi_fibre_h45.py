from sympy import Matrix, GF, __version__
from sympy.polys.matrices import DomainMatrix
from itertools import product
L=Matrix([[-1,1,0],[-1,0,1],[1,0,0]])
assert L.det()==1
mod=lambda m:m.applyfunc(lambda x:x%3)
P=[Matrix(v) for v in product(range(3),repeat=3)]
for t,u,v in product(range(3),repeat=3):
    assert mod(L*Matrix([t,t+u,t+v])+Matrix([1,-1,-1]))==mod(Matrix([u+1,v-1,t-1]))
assert sum(sum(bool(z) for z in p)!=sum(bool(z) for z in mod(L*p)) for p in P)==12
for n in [1,2,3,9,91]:
    M=Matrix(1,n+1,[1]*(n+1))
    rank=DomainMatrix.from_Matrix(M).convert_to(GF(3)).rank()
    assert rank==1
    print('gap',n,'residual nullity per trit',n+1-rank,'total',3*n)
print('SymPy',__version__,'chart and endpoint residual rank PASS')
