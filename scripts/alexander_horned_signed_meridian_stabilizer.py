#!/usr/bin/env python3
"""Exact 48-case signed-permutation stabilizer of [a,b][b,c]."""
from itertools import permutations, product

def reduce_word(xs):
    stack = []
    for x in xs:
        if stack and stack[-1] == -x: stack.pop()
        else: stack.append(x)
    return tuple(stack)

def inverse(xs):
    return tuple(-x for x in reversed(xs))

def cyclic_reduce(xs):
    xs = list(reduce_word(xs))
    while len(xs) > 1 and xs[0] == -xs[-1]: xs = xs[1:-1]
    return tuple(xs)

def conjugate(xs, ys):
    xs, ys = cyclic_reduce(xs), cyclic_reduce(ys)
    return len(xs) == len(ys) and any(xs == ys[i:] + ys[:i] for i in range(len(ys)))

def substitute(xs, p, signs):
    assignment = {i+1: p[i]*signs[i] for i in range(3)}
    return reduce_word(assignment[abs(x)]*(1 if x>0 else -1) for x in xs)

w = (1,2,-1,3,-2,-3)
accepted = []
for p in permutations((1,2,3)):
    for signs in product((1,-1), repeat=3):
        value = substitute(w, p, signs)
        same, reversed_class = conjugate(value,w), conjugate(value,inverse(w))
        if same or reversed_class:
            accepted.append((p,signs,'preserve' if same else 'reverse'))
assert accepted == [
    ((1,2,3),(1,1,1),'preserve'),
    ((1,2,3),(1,-1,1),'reverse'),
    ((3,2,1),(1,1,1),'reverse'),
    ((3,2,1),(1,-1,1),'preserve'),
]
print('PASS: exactly 4 of 48 signed permutations stabilize the unoriented meridian conjugacy class')
for triple in accepted: print(triple)
print('No signed 3-cycle occurs. Geometry and Agda remain unverified.')


# SIX-ABC-ORBIT: reuse the existing S3 permutation enumeration above.
# Strictly oriented parent peripheral classes vs orientation-forgotten
# conjugacy classes. The standard cyclically reduced conjugacy criterion
# is a classical theorem, not an exhaustive finite-word experiment.
def anchor_positive_a(xs):
    xs=cyclic_reduce(xs)
    assert len(xs)==6 and xs.count(1)==1
    i=xs.index(1)
    return xs[i:]+xs[:i]

perms=list(permutations((1,2,3)))
labels=lambda p: ''.join('abc'[i-1] for i in p)
six={labels(p):substitute(w,p,(1,1,1)) for p in perms}
expected={
    'abc':(1,2,-1,3,-2,-3),
    'acb':(1,3,-1,2,-3,-2),
    'bac':(1,-2,3,-1,-3,2),
    'bca':(1,-3,-1,2,3,-2),
    'cab':(1,-3,2,-1,-2,3),
    'cba':(1,-2,-1,3,2,-3),
}
assert {k:anchor_positive_a(v) for k,v in six.items()}==expected
assert len(set(map(anchor_positive_a,six.values())))==6
canonical_unoriented=lambda xs:min(anchor_positive_a(xs),anchor_positive_a(inverse(xs)))
unoriented={canonical_unoriented(v) for v in six.values()}
assert len(unoriented)==3
pairs={}
for p in perms:
    partner=tuple(p[i-1] for i in (3,2,1)) # p after (a c)
    assert conjugate(substitute(w,p,(1,1,1)),
                     inverse(substitute(w,partner,(1,1,1))))
    pairs[labels(p)]=labels(partner)
assert pairs=={'abc':'cba','acb':'bca','bac':'cab',
               'bca':'acb','cab':'bac','cba':'abc'}
for name,v in six.items():
    assert sum(conjugate(v,other) for other in six.values())==1
    assert sum(conjugate(v,inverse(other)) for other in six.values())==1
print('PASS SIX-ABC-ORBIT: 6 distinct oriented peripheral conjugacy classes')
print('PASS SIX-ABC-ORBIT: 3 unoriented classes paired by a<->c')
print('PASS SIX-ABC-ORBIT: exact six anchored normal forms:',expected)
print('NOT PROVED: an embedded 3D stage, all-depth local S3 action, actual basepoint path')
