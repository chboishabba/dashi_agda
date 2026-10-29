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
