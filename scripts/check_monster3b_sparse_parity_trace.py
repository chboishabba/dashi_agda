"""Exact symbolic trace checks on finite signed Weyl fixtures, not MM data."""
from itertools import product
from sympy import Matrix, eye, zeros, QQ
from monster3b_sparse_parity_trace import ranks,require
K=QQ.cyclotomic_field(3);z=K.unit
# Both phase copies of H_s tensor S with an arbitrary parity split,
# plus the original zero phase split. Trace the FULL group action by
# summing fixed coordinates, independently of the sparse formula.
checks=0
for n in (1,2,3):
    X=list(product(range(3),repeat=n));d=len(X)
    for m,p,u,v in ((1,2,2,3),(3,0,0,1),(0,4,5,0),(2,2,0,0)):
        zero=u+v;dim=zero+2*d*(m+p)
        def char(k,b,j):
            total=K.convert(u+((-1)**j)*v)
            for s in (1,2):
                for x in X:
                    y=tuple((-a)%3 for a in x) if j else x
                    if x==y:
                        total+=K.convert(p+((-1)**j)*m)*z**(s*(k+sum(a*c for a,c in zip(b,x))))
            return total
        b0=(0,)*n
        r=ranks(dim,int(K.to_sympy(char(1,b0,0))),int(K.to_sympy(char(0,b0,1))),int(K.to_sympy(char(1,b0,1))),n)
        require((r['negative_rank'],r['positive_rank'],r['zero_sector_j_positive_rank'],r['zero_sector_j_negative_rank'])==(m,p,u,v),'sparse rank mismatch');checks+=1
        for s in (1,2):
            total=sum((z**(-s*k)*char(k,b,1) for k in range(3) for b in X),K.zero)/K.convert(3*d)
            require(total==K.convert(p-m),'full modulation-average residual');checks+=1
        for b in X:
            for k in range(3):
                require(char(k,b,1)==char(k,b0,1),'twisted conjugacy residual');checks+=1
r=ranks(196884,54,276,78)
require((r['negative_rank'],r['positive_rank'],r['zero_sector_j_trace'])==(12,78,144),'target arithmetic');checks+=1
for args in ((196884,54,276,79),(196884,54,276,273),(196884,55,276,78)):
    try:ranks(*args)
    except ValueError:checks+=1
    else:raise ValueError('inconsistent trace accepted')
print({'exact_checks':checks,'status':'SIGNED_WEYL_FIXTURES_ONLY'})
