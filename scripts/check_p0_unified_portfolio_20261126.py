"""Deterministic charged portfolio and retained signed intersection chart."""
from random import Random
from check_p0_future_safe_affine_packet_20261125 import plain, sat, reference
from check_p0_primal_dual_join_20261126 import Budget, Exhausted, recover as parity_recover
from check_p0_projective_child_20261126 import add, recover as projective_recover
from check_p0_affine_resolvent_20261126 import compile_cut, valid
from check_p0_strict_selector_20261126 import recover as strict_recover


def signed_chart(S, budget):
    """Pointwise integer lift of an XOR of affine indicators."""
    Q = {}
    for B in sorted(S):
        budget.pay(); T = dict(Q); add(T, B, 1)
        for A, w in Q.items():
            budget.pay(); add(T, plain(A+B), -2*w)
        Q = T
    return Q


def mass(n, Q, budget):
    z = 0
    for B, w in Q.items():
        budget.pay(); z += w << (n-len(B))
    assert z >= 0
    return z


def pin(Q, i, b, budget):
    T = {}
    for B, w in Q.items():
        budget.pay(); add(T, plain(B+((1<<i,b),)), w)
    return T


def descend(n, Q, budget):
    c = mass(n,Q,budget)
    if not c: return None
    x = 0
    for i in range(n):
        T = pin(Q,i,0,budget); a = mass(n,T,budget)
        assert 0 <= a <= c
        if a: Q,c = T,a
        else: Q = pin(Q,i,1,budget); x |= 1<<i
    assert c == 1
    return x


def intersection_solve(n, rows, f, cap):
    """(x, done): only completed exact charts can report empty."""
    per = cap//(2*(len(f)+1))
    for cut in sorted(range(len(f)+1),key=lambda j:abs(2*j-len(f))):
        try: S = compile_cut(n,rows,f,cut,Budget(per)); break
        except Exhausted: continue
    else: return None,False
    try:
        B = Budget(cap//2); Q = signed_chart(S,B); x = descend(n,Q,B)
        if x is not None: assert valid(x,n,rows,f)
        return x,True
    except Exhausted: return None,False


def portfolio(n, rows, f, cap):
    """Fixed shares; only exact empty routes may return done with no witness."""
    from check_pnp_affine_normal_components import cnf_flats, recover as component
    from check_pnp_normal_transversal import solve as transversal
    allowance = cap//6
    F = cnf_flats(f)
    x, _, done = transversal(n,rows,F,allowance)
    if done:
        if x is not None: assert valid(x,n,rows,f)
        return x,True,'transversal-boundary'
    x,_ = component(n,rows,F,allowance)
    if x is not None:
        assert valid(x,n,rows,f); return x,True,'components'
    for name, solve in [('parity',parity_recover),('strict',strict_recover),('projective',projective_recover)]:
        x = solve(n,rows,f,allowance)
        if x is not None:
            assert valid(x,n,rows,f); return x,True,name
    x,done = intersection_solve(n,rows,f,allowance)
    return x,done,'signed-intersections' if done else 'unknown'


def main():
    rng=Random(96); charts=cuts=inhabited=empty=0
    for n in range(8):
        for _ in range(50):
            S=set()
            for j in range(rng.randrange(9)):
                B=plain(tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1))))
                if B is not None: S.symmetric_difference_update((B,))
            B=Budget(1000000); Q=signed_chart(S,B)
            truth=[]
            for x in range(1<<n):
                v=sum(all((a&x).bit_count()%2==b for a,b in C) for C in S)%2
                assert v==sum(w for C,w in Q.items() if all((a&x).bit_count()%2==b for a,b in C))
                if v:truth.append(x)
            assert mass(n,Q,B)==len(truth)
            x=descend(n,Q,B); assert (x in truth) if truth else x is None
            charts+=1
            rows=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(n,3)+1))) for _ in range(rng.randrange(7))]
            _,c=reference(n,rows,f)
            for cut in range(len(f)+1):
                B=Budget(1000000); S=compile_cut(n,rows,f,cut,B)
                assert mass(n,signed_chart(S,B),B)==c;cuts+=1
            x,done=intersection_solve(n,rows,f,2000000)
            assert done and (x is not None)==bool(c)
            if c: assert valid(x,n,rows,f);inhabited+=1
            else:empty+=1
    # Exponential subset expansion, but only linearly many distinct intersections.
    for n in (16,32,64,128):
        S={tuple((1<<i,0) for i in reversed(range(k))) for k in range(n+1)}
        B=Budget(1000000);Q=signed_chart(S,B);assert len(Q)<=n+1
        expected=sum(1<<(n-k-1) for k in range(0,n,2)) + int(n%2==0)
        assert mass(n,Q,B)==expected
        assert descend(n,Q,B) is not None
    assert intersection_solve(3,(),[],0)==(None,False)
    assert intersection_solve(3,(),[()],1000)==(None,True)
    # Distinct flats can be pointwise XOR-zero: whole plane plus two siblings.
    B=Budget(1000);assert mass(3,signed_chart({(),((1,0),),((1,1),)},B),B)==0
    print(dict(charts=charts,cut_comparisons=cuts,inhabited=inhabited,empty=empty,nested_controls=4,controls='PASS'))

if __name__=='__main__': main()
