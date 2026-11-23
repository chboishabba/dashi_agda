"""Independent finite reference; not a physical KK or atomic Hamiltonian."""
from itertools import product, permutations
import sympy as s

def laplacian(n, edges):
    L=s.zeros(n)
    for i,j in edges:
        v=s.eye(n)[:,i]-s.eye(n)[:,j]
        L+=v*v.T
    return L

def main():
    pts=list(product(range(3),repeat=3))
    edges=[(i,j) for i,a in enumerate(pts) for j,b in enumerate(pts) if i<j and sum(abs(x-y) for x,y in zip(a,b))==1]
    cube=laplacian(27,edges)
    circle=laplacian(27,[(i,(i+1)%27) for i in range(27)])
    assert len(edges)==54
    assert s.trace(cube)==108 and s.trace(circle)==54
    assert cube*s.ones(27,1)==circle*s.ones(27,1)==s.zeros(27,1)
    # Signed proper and improper frames on a labelled tetrahedron.
    X=s.diag(1,2,3); G=X.T*X
    n=0
    for p in permutations(range(3)):
        for signs in product((-1,1),repeat=3):
            R=s.zeros(3)
            for i,j in enumerate(p): R[i,j]=signs[i]
            Y=R*X
            assert Y.T*Y==G and Y.det()==R.det()*X.det()
            n+=1
    # A compact-circle character sampled on 27 sites aliases n and n+27.
    # Exact rational phase turns modulo one, no numerical complex rounding.
    aliases=0
    for k in range(-13,14):
        for j in range(27):
            assert (s.Rational(k*j,27)%1)==(s.Rational((k+27)*j,27)%1)
            assert k*k!=(k+27)**2
            aliases+=1
    # Spectral invariants of two different 27-site operators, exact integers.
    print(f'cube edges={len(edges)}; traces={s.trace(cube)},{s.trace(circle)}; signed frames={n}; alias cases={aliases}; PASS')
if __name__=='__main__': main()
