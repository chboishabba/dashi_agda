#!/usr/bin/env python3
"""Exact polynomial reference for GRH signed phase observation recovery.
No analytic zero-sum or kernel acceptance is implied.
"""
from math import comb
import sympy as s


def recover_projective(m, samples):
    """Recover H exactly from (ratio y/x at x=1, phase value) pairs."""
    if not isinstance(m, int) or m < 1 or len(samples) != m//2+1:
        raise ValueError('wrong homogeneous degree or number of samples')
    u = s.Symbol('u')
    points = []
    for t, value in samples:
        t, value = s.sympify(t), s.sympify(value)
        if t.is_Rational is not True or value.is_Rational is not True or t < 0:
            raise ValueError('nonnegative exact rational ratio and rational value required')
        scale = (1-t)**(m%2)*(1+t)**(m-m%2)
        if scale == 0:
            raise ValueError('antisymmetric diagonal is not an observation')
        points.append((t/(1+t)**2, value/scale))
    if len({v for v,_ in points}) != len(points):
        raise ValueError('aliased projective ratios')
    return s.Poly(s.interpolate(points, u), u, domain=s.QQ)


def weighted_mixed(m, points):
    """Exact obstruction for the old sixth/eighth slices; points=(w,x,y)."""
    if m not in (3,4):
        raise ValueError('selected sixth/eighth mixed fibre only')
    total = s.S.Zero
    for point in points:
        w,x,y = map(s.sympify, point)
        if not all(v.is_Rational is True for v in (w,x,y)):
            raise ValueError('exact rational weighted points required')
        total += w*x*y*(x-y)**(1 if m==3 else 2)
    return total


def check():
    x, y, A, B, C = s.symbols('x y A B C')
    f6 = A*(x**3-y**3)+C*x*y*(x-y)
    f8 = A*(x*x-y*y)**2+B*x*x*y*y+C*x*y*(x-y)**2
    obs = lambda f, t: f.subs({x: 1, y: t})
    a, t = obs(f6, 0), obs(f6, 2)
    assert s.expand(-(t+7*a)/2-C) == 0
    assert obs(f6, 1) == 0
    a,b,t = (obs(f8, z) for z in (0,1,2))
    assert s.expand((t-9*a-4*b)/2-C) == 0
    for f,m,coeff in [(f6,3,{A:1,C:-15}), (f8,4,{A:1,B:16,C:-28})]:
        p=sum((-1)**j*comb(2*m,2*j)*x**(m-j)*y**j for j in range(m+1))
        assert s.expand(f.subs(coeff)-p)==0
        assert s.expand(p.xreplace({x:y,y:x})-(-1)**m*p)==0
    for f in (f6,f8):
        invisible=s.diff(f,C)
        assert obs(invisible,0)==obs(invisible,1)==0
        assert abs(obs(invisible,2))==2
    # All orders: normalized projective coordinate u=xy/(x+y)^2.
    # F = (x+y)^m H(u) even; F = (x-y)(x+y)^(m-1) H(u) odd.
    for m in range(1,33):
        k=m//2
        basis=[(x-y)**(m%2)*(x+y)**(m-m%2-2*j)*(x*y)**j for j in range(k+1)]
        # Axis plus k positive non-diagonal ratios (odd); even also uses diagonal.
        ratios=[0]+(list(range(1,k+1)) if m%2==0 else list(range(2,k+2)))
        M=s.Matrix([[obs(g,t) for g in basis] for t in ratios])
        us=[s.Rational(t,(1+t)**2) for t in ratios]
        scales=[(1-t)**(m%2)*(1+t)**(m-m%2) for t in ratios]
        vand=s.Matrix([[u**j for j in range(k+1)] for u in us])
        assert M==s.diag(*scales)*vand
        assert len(set(us))==k+1 and all(scales)
        assert M.rank()==k+1
        p=sum((-1)**j*comb(2*m,2*j)*x**(m-j)*y**j for j in range(m+1))
        coef=M.inv()*s.Matrix([obs(p,t) for t in ratios])
        h=recover_projective(m, [(t, obs(p,t)) for t in ratios])
        assert [h.nth(j) for j in range(k+1)]==list(coef)
        assert s.expand(sum(c*g for c,g in zip(coef,basis))-p)==0
        # Drop any one scalar sample: a nonzero invisible polynomial remains.
        for i in range(k+1):
            reduced=M.copy(); reduced.row_del(i)
            assert len(reduced.nullspace())==1
    # A weighted observer only descends iff it annihilates the invisible direction.
    for f in (f6,f8):
        residual=s.diff(f,C)
        assert s.expand((f.subs(C,C+1)-f)-residual)==0
        # Equal/opposite signed weighted samples: parity matters.
        swapped=residual.xreplace({x:y,y:x})
        expected=-1 if f==f6 else 1
        assert s.expand(swapped-expected*residual)==0
    same=[(1,1,2),(1,2,1)]
    opposite=[(1,1,2),(-1,2,1)]
    assert weighted_mixed(3,same)==0 and weighted_mixed(4,same)==4
    assert weighted_mixed(3,opposite)==-4 and weighted_mixed(4,opposite)==0
    for m,samples in [(3,[(0,0),(1,0)]), (4,[(0,0),(2,0),(s.Rational(1,2),0)]), (4,[(0,0)])]:
        try:
            recover_projective(m,samples)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid observation accepted')
    print('PASS: sixth/eighth inverse and physical phases; signed lost-mode controls; 32 all-order projective recovery layers and 288 deletion tests; weighted parity controls')

if __name__=='__main__':
    check()
