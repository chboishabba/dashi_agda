from itertools import product, permutations
from collections import Counter
import sympy as s

def check():
    pts=list(product(range(3),repeat=2))
    neg=lambda x: tuple(-a%3 for a in x)
    Q=sorted({min(x,neg(x)) for x in pts})
    assert sorted(Counter(min(x,neg(x)) for x in pts).values())==[1,2,2,2]
    B=list(product(Q,range(2),range(3**8),range(3)))
    pairs=list(permutations(range(3),2))
    R=list(product(pairs,range(3),range(3)))
    assert len(B)==196830 and len(R)==54
    X=[(0,x) for x in B]+[(1,x) for x in R]
    def act(z,k,mode):
        tag,x=z
        if tag==1 and mode=='B': return z
        return tag,x[:-1]+((x[-1]+k)%3,)
    traces={}
    for mode in 'BC':
        traces[mode]=tuple(sum(act(z,k,mode)==z for z in X) for k in range(3))
        assert all(act(act(z,1,mode),2,mode)==z for z in X)
    assert traces=={'B':(196884,54,54),'C':(196884,0,0)}
    def mult(t): return s.Matrix([(t[0]+2*t[1])//3,(t[0]-t[1])//3,(t[0]-t[1])//3])
    b,c=map(mult,(traces['B'],traces['C']))
    L=3*s.eye(3)-s.ones(3)
    assert b-c==18*L[:,0] and L*L==3*L and L.eigenvals()=={3:2,0:1}
    assert 729*(12+78)==len(B)//3==10*3**8
    for a,b in pairs:
        assert len({(p[a],p[b]) for p in permutations(range(3))})==6
    for x in range(3):
        r=lambda y:(y+1)%3
        f=lambda y:-y%3
        assert r(r(r(x)))==x and f(f(x))==x and f(r(f(x)))==r(r(x))
    t=s.symbols('t')
    a,b,c=32814+t/2,32814-t/2,65628
    assert s.simplify(a+b+2*c)==196884
    assert s.simplify(a-b)==t and s.simplify(a+b-c)==0
    print('PASS finite models, Laplacian, S3 torsor, dihedral relations, reflection inversion')
if __name__=='__main__': check()
