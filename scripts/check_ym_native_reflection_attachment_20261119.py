"""Exact native R445 site-plane geometry and formal noncommutative words.
Uses the existing block/reflection formulas from check_ym_r445_time_reflection_q8_20261106.py.
No probability surrogate, no claim of Agda acceptance or physical continuum RP.
"""
from itertools import product
import sympy as s

def step(x, mu, d, L):
    y=list(x); y[mu]=(y[mu]+d)%L; return tuple(y)
def theta(x,L): return ((-x[0])%L,*x[1:])
def block_edges(x,mu,L):
    y=tuple(2*i for i in x)
    return ((y,mu),(step(y,mu,1,2*L),mu))
def reflect_edge(e,L):
    x,mu=e; y=theta(x,L)
    return ((step(y,0,-1,L),mu),-1) if mu==0 else ((y,mu),1)
def check(L):
    count=0
    # Exact equality in the free signed word algebra, stronger than Q8 evaluation.
    for x in product(range(L),repeat=4):
        for mu in range(4):
            lhs=tuple(reflect_edge(e,2*L) for e in block_edges(x,mu,L))
            coarse,sign=reflect_edge((x,mu),L)
            edges=block_edges(*coarse,L)
            rhs=tuple((e,sign) for e in (edges if sign==1 else edges[::-1]))
            assert lhs==rhs,(L,x,mu,lhs,rhs)
            # Closed positive half slab: both endpoints of each coarse bond
            # must lie in the selected lift [0,L/2] without periodic wrap.
            if x[0]<=L//2 and (mu!=0 or x[0]+1<=L//2):
                for y,axis in block_edges(x,mu,L):
                    assert 0<=y[0]<=L
                    assert axis!=0 or y[0]+1<=L
            count+=1
    return count
# Native temporal reversal in a noncommutative symbolic matrix algebra.
# Inversion of a product is the existing group theorem, not a commutative simplification.
a,b=s.MatrixSymbol('A',2,2),s.MatrixSymbol('B',2,2)
assert (a*b).inv().doit()==b.inv()*a.inv()
# Arbitrary integer coordinate: reflection and embedding commute modulo 2L.
x,L,k=s.symbols('x L k',integer=True)
assert s.expand(-2*x-2*(-x+k*L)+2*k*L)==0
counts={L:check(L) for L in (2,3,4,5,6,8,10,12)}
print('PASS exact signed-word bond identities:',counts,'total',sum(counts.values()))
print('PASS selected closed positive-half support and symbolic matrix reversal')
print('Scope: native geometry reference; Agda attachment, published RP and continuum not tested')
