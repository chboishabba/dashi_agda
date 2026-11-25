"""R395-R398: source-side promise-aware autarky reduction and packed spectral output.
Exhaustive enumeration appears only in reference tests. LP candidates from HiGHS are reconstructed and checked exactly in SymPy.
The theoretical bound uses rational polynomial-time LP, not the numerical backend.
"""
from collections import deque, Counter
from itertools import product
from random import Random
from sympy import Matrix, zeros, ones, Rational
from scipy.optimize import linprog
from fractions import Fraction
import numpy as np


def normalize(f):
    return tuple(c for c in (tuple(sorted(set(c))) for c in f)
                 if not any(-l in c for l in c))


def satisfied(f, x):
    return all(any(x[abs(l)] == int(l > 0) for l in c) for c in f)


def restrict(f, p):
    return tuple(tuple(l for l in c if abs(l) not in p) for c in f
                 if not any(p.get(abs(l)) == int(l > 0) for l in c))


def autarky_check(f, p):
    return all(not any(abs(l) in p for l in c) or
               any(p.get(abs(l)) == int(l > 0) for l in c) for c in f)


def matching_autarky(f, variables):
    adj = [sorted({abs(l) for l in c}) for c in f]
    cv, vc = {}, {}
    # Iterative augmenting paths, no recursion depth assumption.
    for c0 in range(len(f)):
        queue, prev, visited = deque([c0]), {}, {c0}
        end = None
        while queue and end is None:
            c = queue.popleft()
            for v in adj[c]:
                if v in prev:
                    continue
                prev[v] = c
                if v not in vc:
                    end = v
                    break
                k = vc[v]
                if k not in visited:
                    visited.add(k); queue.append(k)
        while end is not None:
            c = prev[end]; old = cv.get(c)
            cv[c] = end; vc[end] = c
            end = old
    rc = set(range(len(f))) - set(cv); rv = set(); queue = deque(sorted(rc))
    while queue:
        c = queue.popleft()
        for v in adj[c]:
            if v in rv:
                continue
            rv.add(v)
            assert v in vc  # maximal matching has no augmenting path
            k = vc[v]
            if k not in rc:
                rc.add(k); queue.append(k)
    p = {v: 0 for v in variables if v not in rv}
    for c in set(range(len(f))) - rc:
        v = cv[c]; assert v in p
        l = next(l for l in f[c] if abs(l) == v)
        p[v] = int(l > 0)
    assert autarky_check(f, p)
    # Residual matching covers all remaining variables, and each reached
    # variable lies on an alternating path from an unmatched residual clause.
    assert set(variables)-set(p) == rv
    assert all(vc[v] in rc for v in rv)
    assert all(not any(abs(l) in p for l in f[c]) for c in rc)
    return p


def signed_matrix(f, variables):
    return Matrix([[int(v in c)-int(-v in c) for v in variables] for c in f])


def linear_autarky(f, variables):
    A = signed_matrix(f, variables)
    n, m = len(variables), len(f)
    ker = A.nullspace()
    if ker:
        v = ker[0]
    else:
        # Numerical discovery only; exact primal or dual certificates are mandatory.
        arr = np.array(A.tolist(),dtype=float)
        opt = linprog(-arr.sum(axis=0), A_ub=-arr, b_ub=np.zeros(m),
                      bounds=[(-1,1)]*n, method='highs')
        if not opt.success: return {}, None
        v = Matrix([Rational(Fraction(float(x)).limit_denominator(10**6)) for x in opt.x])
        if not all(a>=0 for a in A*v): return {}, None
        if not any(v):
            opt = linprog(np.zeros(m), A_eq=arr.T, b_eq=np.zeros(n),
                          bounds=[(1,None)]*m, method='highs')
            if not opt.success: return {}, None
            y = Matrix([Rational(Fraction(float(x)).limit_denominator(10**6)) for x in opt.x])
            if not (all(a>=1 for a in y) and A.T*y==zeros(n,1) and A.rank()==n): return {}, None
            return {}, (A,y)
    assert any(v) and all(a>=0 for a in A*v)
    p = {k:int(bool(a>0)) for k,a in zip(variables,v) if a!=0}
    assert autarky_check(f,p)
    return p, None


def packed(n,p):
    assert set(p)==set(range(1,n+1))
    M=1<<(n+2); Q=4*M
    z=[pow(5,1<<i,M) for i in range(n)]
    A=1
    for t in z: A=A*(1+t)%Q
    a=sum(p[i]<<(i-1) for i in p)
    return (3*A-4*pow(5,a,M))%Q


def produce(f,n,use_linear=True):
    """Return SAT witness/residue (exact under singleton), UNSAT, or UNKNOWN.
    SAT is always verified; no uniqueness certification is attempted.
    """
    original=tuple(f); f=normalize(f); V=set(range(1,n+1)); p={}; steps=Counter()
    while True:
        if () in f: return 'UNSAT',None,None,steps
        if not f:
            p.update({v:0 for v in V}); assert satisfied(original,p)
            return 'SAT',p,packed(n,p),steps
        units={}
        for c in f:
            if len(c)==1:
                l=c[0]; v=abs(l); b=int(l>0)
                if v in units and units[v]!=b: return 'UNSAT',None,None,steps
                units[v]=b
        if units: q=units; kind='unit'
        else:
            q=matching_autarky(f,V); kind='matching'
            if not q:
                signs={v:{int(l>0) for c in f for l in c if abs(l)==v} for v in V}
                q={v:next(iter(s)) for v,s in signs.items() if len(s)==1}; kind='pure'
            if not q and use_linear:
                q,cert=linear_autarky(f,sorted(V)); kind='linear'
                if not q and cert is None: steps['uncertified_lp']+=1
        if not q: return 'UNKNOWN',p,None,steps
        steps[kind]+=len(q); assert set(q)<=V
        if kind!='unit': assert autarky_check(f,q)
        f=restrict(f,q); V-=set(q); p.update(q)


def models(f,n):
    return [dict(enumerate(x,1)) for x in product((0,1),repeat=n) if satisfied(f,dict(enumerate(x,1)))]


def ref_moment(f,n):
    M=1<<(n+2); Q=4*M
    A=1
    for i in range(n): A=A*(1+pow(5,1<<i,M))%Q
    W=sum(pow(5,sum(x[i]<<(i-1) for i in x),M) for x in models(f,n))
    return (3*A-4*W)%Q


def main():
    rng=Random(395); outcomes=Counter(); steps=Counter(); singleton=Counter(); matching_checks=0
    for n in range(1,7):
        for _ in range(35):
            f=tuple(tuple(rng.choice((-1,1))*v for v in rng.sample(range(1,n+1),rng.randint(1,min(3,n)))) for _ in range(rng.randrange(0,3*n+1)))
            ws=models(f,n); status,p,d,st=produce(f,n)
            outcomes[status]+=1; steps.update(st)
            if status=='UNSAT': assert not ws
            if status=='SAT': assert p in ws
            if len(ws)==1:
                singleton[status]+=1
                if status=='SAT': assert p==ws[0] and d==ref_moment(f,n)
                else: assert status=='UNKNOWN' and all(ws[0][v]==b for v,b in p.items())
            # Exhaustively check strict Hall expansion on matching residual.
            g=normalize(f); q=matching_autarky(g,set(range(1,n+1))); h=restrict(g,q)
            V=sorted(set(range(1,n+1))-set(q))
            for mask in range(1,1<<len(V)):
                S={v for i,v in enumerate(V) if mask>>i&1}
                assert sum(any(abs(l) in S for l in c) for c in h)>=len(S)+1
                matching_checks+=1
    # Connected singleton with no units/pure literals, matching-lean and zero signed cone.
    # On consecutive triples require all zero: forbid the seven other assignments.
    for n in (3,6,12,24):
        f=tuple(tuple(i+j+1 if bit==0 else -(i+j+1) for j,bit in enumerate(x))
                for i in range(n-2) for x in product((0,1),repeat=3) if any(x))
        assert not matching_autarky(f,set(range(1,n+1)))
        q,cert=linear_autarky(f,list(range(1,n+1))); assert not q and cert is not None
        status,p,d,_=produce(f,n); assert status=='UNKNOWN' and p=={} and d is None
        assert satisfied(f,{v:0 for v in range(1,n+1)})
        if n<=6: assert len(models(f,n))==1
    # Linear autarky beyond matching and pure literals: 2-CNF equivalent to all zero.
    f=((-1,-2),(-1,2),(1,-2))
    assert not matching_autarky(f,{1,2})
    p,cert=linear_autarky(f,[1,2]); assert p=={1:0,2:0} and cert is None
    status,p,d,st=produce(f,2); assert status=='SAT' and st['linear']==2 and d==ref_moment(f,2)
    # Large source-side positive families: equality chains with an original unit;
    # no witness supplied, producer must actually recover all bits.
    for n in (32,128,512):
        witness=[rng.randrange(2) for _ in range(n)]
        f=[(1 if witness[0] else -1,)]
        for i in range(1,n):
            a=i if witness[i-1] else -i; b=i+1 if witness[i] else -(i+1)
            f.extend([(-a,b),(a,-b)])
        status,p,d,st=produce(f,n)
        assert status=='SAT' and list(p[i] for i in range(1,n+1))==witness and d==packed(n,p)
    # Connected non-unit singleton families: each adjacent pair forbids 01,10,11.
    # No witness, units or pure literals are supplied; the signed cone finds it.
    for n in (16,32):
        f=tuple(c for i in range(1,n) for c in ((-i,-i-1),(-i,i+1),(i,-i-1)))
        assert not matching_autarky(f,set(range(1,n+1)))
        status,p,d,st=produce(f,n)
        assert status=='SAT' and st['linear']==n and not any(p.values()) and d==packed(n,p)
    # Empty formula/free variables: witness-only output is not unrestricted moment.
    status,p,d,_=produce((),3); assert status=='SAT' and d!=ref_moment((),3)
    print(dict(random=outcomes,singletons=singleton,assigned=steps,hall_subset_checks=matching_checks,
               zero_cone_singletons=4,linear_beyond_matching=1,large_source_instances=3,nonunit_linear_chains=2,multi_firewall=1))


if __name__=='__main__':
    main()
