from itertools import product, permutations
from collections import Counter
import sympy as s

def enc(a): return tuple((v!=0,v if v else None) for v in a)
def dec(a): return tuple(v if m else 0 for m,v in a)
def rot(a): return tuple(a[i+j] for i in range(0,len(a),3) for j in (1,2,0))
def step(state,axis):
    a,b,e=state
    if axis=='x': return (a[:6],a[6:],e)
    if axis=='y': return (rot(a),rot(b),e)
    if axis=='z': return (enc(a),enc(b),True)
def run(state,order):
    for axis in order: state=step(state,axis)
    return state
orders=list(permutations('xyz')); faces=Counter(); endpoints=0
for a in product((-1,0,1),repeat=9):
    initial=(a,(),False)
    for i,j,k in [('x','y','z'),('x','z','y'),('y','z','x')]:
        for upper in (False,True):
            st=run(initial,k) if upper else initial
            assert run(st,i+j)==run(st,j+i)
            faces[i+j+str(int(upper))]+=1
    results=[run(initial,p) for p in orders]
    assert all(v==results[0] for v in results)
    for p,b,e in results:
        assert dec(p)+dec(b)==rot(a)
        endpoints+=1
# SymPy permutation matrix on nine coordinates, preserving each triple.
R=s.zeros(9)
for i in range(9): R[i,3*(i//3)+(i+1)%3]=1
assert R**3==s.eye(9)
Q=s.eye(9)[:6,:]
assert Q*R==R[:6,:6]*Q
assert enc((1,0,-1))!=enc((-1,0,1))
print('SymPy',s.__version__,'faces',dict(faces),'endpoint roundtrips',endpoints,'rotation and prefix PASS')
