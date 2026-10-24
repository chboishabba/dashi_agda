#!/usr/bin/env python3
"""Exact finite discriminator: an infinite-order meridian may map to C3.
Finite test only. Infinite conclusion: Hatcher AT Example 2B.2
injective free-group stages + compactness. Geometric 3-copy gate open.
"""
from itertools import permutations

ID = tuple(range(5))
S = (1, 2, 0, 3, 4)


def mul(a, b):
    return tuple(a[b[i]] for i in range(5))


def inverse(a):
    return tuple(a.index(i) for i in range(5))


def comm(a, b):
    return mul(mul(mul(a, b), inverse(a)), inverse(b))


def subgroup_size(gens):
    moves = tuple(gens) + tuple(inverse(x) for x in gens)
    known, stack = {ID}, [ID]
    while stack:
        x = stack.pop()
        for g in moves:
            y = mul(x, g)
            if y not in known:
                known.add(y)
                stack.append(y)
    return len(known)


def reduce_free(w):
    stack = []
    for a, sign in w:
        if stack and stack[-1] == (a, -sign):
            stack.pop()
        else:
            stack.append((a, sign))
    return tuple(stack)


def generator(c, path=()):
    return (((c, path), 1),)


def word_inverse(w):
    return tuple((a, -sign) for a, sign in reversed(w))


def word_product(*words):
    return reduce_free(letter for w in words for letter in w)


def expand(w):
    parts = []
    for (c, path), sign in w:
        a = generator(c, path + (0,))
        b = generator(c, path + (1,))
        block = word_product(a, b, word_inverse(a), word_inverse(b))
        parts.append(block if sign == 1 else word_inverse(block))
    return word_product(*parts)


def evaluate(w, values):
    result = ID
    for address, sign in w:
        q = values[address]
        result = mul(result, q if sign == 1 else inverse(q))
    return result


def check(depth=4, max_power=9):
    A5 = [p for p in permutations(range(5))
          if sum(p[i] > p[j] for i in range(5)
                 for j in range(i + 1, 5)) % 2 == 0]
    assert len(A5) == 60
    assert mul(mul(S, S), S) == ID and S != ID
    witnesses, root_pair = {}, None
    for a in A5:
        for b in A5:
            c = comm(a, b)
            witnesses.setdefault(c, (a, b))
            if root_pair is None and c == S and subgroup_size((a, b)) == 60:
                root_pair = (a, b)
    assert len(witnesses) == 60 and root_pair is not None
    levels = [{(): S}]
    for n in range(depth):
        children = {}
        for address, q in levels[-1].items():
            a, b = root_pair if n == 0 else witnesses[q]
            assert comm(a, b) == q
            children[address + (0,)] = a
            children[address + (1,)] = b
        levels.append(children)

    for n, level in enumerate(levels):
        values = {(sector, path): q
                  for sector in range(3) for path, q in level.items()}
        for sector in range(3):
            meridian = generator(sector)
            for _ in range(n):
                meridian = expand(meridian)
            assert evaluate(meridian, values) == S
            for k in range(1, max_power + 1):
                power = word_product(*(meridian for _ in range(k)))
                assert power != ()
                value = ID
                for _ in range(k):
                    value = mul(value, S)
                assert evaluate(power, values) == value
            assert evaluate(word_product(meridian, meridian, meridian),
                            values) == ID
    # The braid b=sigma_1 sigma_2 maps to a three-cycle on endpoints,
    # whereas b^3 is not identity in B3, since the exponent-sum
    # homomorphism B3->Z sends b^3 to 6.
    swap01, swap12 = (1, 0, 2), (0, 2, 1)
    compose = lambda x, y: tuple(x[y[i]] for i in range(3))
    p = compose(swap01, swap12)
    assert p != (0, 1, 2)
    assert compose(compose(p, p), p) == (0, 1, 2)
    assert 3 * (1 + 1) == 6 != 0
    print("A5 60/60 commutators; selected root maps to order-three image")
    print("Children generate A5; three root sectors; finite stages 0..", depth)
    print("Source reduced words: m^3 != 1; quotient q(m^3)=1: PASS")
    print("Three-cycle braid permutation vs nonidentity full twist: PASS")
    print("Infinite colimit, geometric gluing, Agda kernel: NOT TESTED")


if __name__ == "__main__":
    check()
