from itertools import product
from sympy import Matrix, trace
U = Matrix([[1,1],[0,1]])
V = Matrix([[1,0],[1,1]])
W = Matrix([[1,2],[0,1]])
P=U*V*W
Q=V*W*U
assert P != Q
assert Q == U.inv()*P*U
assert trace(P)==trace(Q)
assert U.det()==V.det()==W.det()==1

# Original RH source frame coordinates: index, tagged phase, sign,
# residual, observed-zero. This is a finite fixture, not analytic zeta.
modes = ('scalarZero','one','zeta','zetaSquared')
def reflect(f):
    k,m,s,r,z=f
    return (k,{'scalarZero':'scalarZero','one':'one','zeta':'zetaSquared','zetaSquared':'zeta'}[m],s,r,z)
def flux(f, delta):
    k,m,s,r,z=f
    return (k+1,m,s,r+delta,z)
checks=0
for k,m,s,r,z in product(range(10),modes,(-1,1),(0,9,13),(False,True)):
    f=(k,m,s,r,z)
    assert flux(reflect(f),4)==reflect(flux(f,4))
    assert reflect(reflect(f))==f
    assert flux(flux(f,4),5)[3]==r+9
    checks+=1
# A non-equivariant phase update demonstrably fails the RH square.
def biased(f):
    k,m,s,r,z=f
    return (k+1,'zeta' if m=='zetaSquared' else m,s,r,z)
assert biased(reflect((0,'zeta',1,9,True))) != reflect(biased((0,'zeta',1,9,True)))
print('PASS nonabelian ordered product differs; cyclic conjugacy & trace')
print('PASS',checks,'indexed RH flux/reflection cases; biased-step rejection')
