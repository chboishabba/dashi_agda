"""G105–G109: exact finite policy/repair tests, not a Clay separation."""
from itertools import product
from sympy import symbols, expand

n = 3
nodes = [p for k in range(n) for p in product((0, 1), repeat=k)]
leaves = list(product((0, 1), repeat=n))
index = {p:i for i,p in enumerate(nodes)}
leafindex = {p:i for i,p in enumerate(leaves)}

def route(policy, p):
    while len(p) < n:
        p += ((policy >> index[p]) & 1,)
    return p

checks = defects = repairs = changed = 0
for policy in range(1 << len(nodes)):
    routes = {p:route(policy,p) for p in nodes+leaves}
    for mask in range(1 << len(leaves)):
        f = lambda p: (mask >> leafindex[p]) & 1
        S = {p:f(x) for p,x in routes.items()}
        local = []
        for p in nodes:
            c = (policy >> index[p]) & 1
            chosen, other = p+(c,), p+(1-c,)
            d = S[p] - (S[chosen] | S[other])
            assert S[p] == S[chosen]
            assert d == -(1-S[chosen])*S[other]
            if d:
                assert S[p] == 0 and f(routes[other]) == 1
                assert routes[other][:len(p)] == p
                local.append(p); defects += 1
                # Flip this policy bit; all other node choices are unchanged.
                newpolicy = policy ^ (1 << index[p])
                for q in nodes+leaves:
                    enters = len(q)<=len(p) and routes[q][:len(p)] == p and p[:len(q)] == q
                    newroute = route(newpolicy,q)
                    assert f(newroute)-S[q] == int(enters)
                    repairs += 1
                    changed += int(enters)
            checks += 1
        for p in nodes+leaves:
            actual = any(f(x) for x in leaves if x[:len(p)]==p)
            # A descendant defect is necessary for an incorrect node;
            # a correct node may still have descendant defects.
            if actual and not S[p]:
                assert any(q[:len(p)]==p for q in local)
        assert (not local) == all(S[p] == any(f(x) for x in leaves if x[:len(p)]==p) for p in nodes+leaves)
print('policies', 1<<len(nodes), 'truth tables', 1<<len(leaves))
print('local identities', checks, 'constructive defects', defects)
print('repair face checks', repairs, 'positive repairs', changed)
# Exact Boolean polynomial for the one-sided discrepancy.
a,b=symbols('a b')
assert expand(a-(a+b-a*b)+(1-a)*b)==0
# Source-indexed comparison: signed deltas transport by ordinary difference.
u,v,w,z=symbols('u v w z')
assert expand((z-v)-(w-u)-((z-w)-(v-u)))==0
print('SymPy identities 2/2')
