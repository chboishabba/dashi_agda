import itertools as it
import sympy as s
from fractions import Fraction as F

def run():
    counts = dict(laplace=0, pivot=0, dickson=0, phase=0, helical=0)
    for rates in it.product(range(1,4), repeat=3):
        for m in it.product(range(-2,3), repeat=3):
            q = sum(F(2*m[i]*m[j], rates[i]+rates[j]) for i in range(3) for j in range(3))
            h = sum(m)**2
            assert q >= 0
            c = sum((F(1,2)-F(1,rates[i]+rates[j]))*2*m[i]*m[j] for i in range(3) for j in range(3))
            assert c == h-q and c <= h
            counts['laplace'] += 1
    for a0,a1,b0,b1 in it.product(range(-3,4), repeat=4):
        if a0*a1 == 0: continue
        assert -F(b1,a1)+F(b0,a0) == F(b0*(a1-a0)-a0*(b1-b0),a0*a1)
        counts['pivot'] += 1
    a,y,z=s.symbols('a y z', nonzero=True)
    B=-3*a*a+3*a+1
    Q=-3*a**3-3*a*a*z-a*a+3*a*z+3*a-2*z*z+z+3
    D=B*B+8*(-3*a**3-a*a+3*a+3-y-a**7/y)
    d=B-4*z
    assert s.cancel(d*d-D+8*(Q-y-a**7/y)) == 0
    assert s.expand((B-d)/4-z)==0
    counts['dickson']+=2
    # Exact character sums in Z[X]/(X^2+X+1), represented by pairs.
    w=((1,0),(0,1),(-1,-1))
    def add(v): return tuple(map(sum,zip(*v)))
    def mul(u,v): return (u[0]*v[0]-u[1]*v[1],u[0]*v[1]+u[1]*v[0]-u[1]*v[1])
    for a,b,c in it.product(range(3), repeat=3):
        got=add(w[(a*x*x+b*x+c)%3] for x in range(3))
        expected=(0,0) if a==0 and b else ((3*w[c][0],3*w[c][1]) if a==0 else mul(w[(c-b*b*a)%3],add(w[(a*x*x)%3] for x in range(3))))
        assert got==expected
        counts['phase']+=1
    # Polarized product rule on the swap-paired double mixed cell.
    t=s.symbols('t', real=True)
    u=s.Matrix([t,t*t,1]); v=s.Matrix([1,t,t**3]); p=s.Matrix([t**2,1,t]); q=s.Matrix([t**3,t,1])
    m=2*(u.cross(v)+p.cross(q))
    rhs=2*(u.diff(t).cross(v)+u.cross(v.diff(t))+p.diff(t).cross(q)+p.cross(q.diff(t)))
    assert all(s.expand(x)==0 for x in m.diff(t)-rhs)
    counts['helical']+=3
    return counts

if __name__=='__main__':
    if not __debug__: raise SystemExit('refusing optimized execution')
    counts=run()
    print(counts, 'TOTAL', sum(counts.values()), 'PASS')
