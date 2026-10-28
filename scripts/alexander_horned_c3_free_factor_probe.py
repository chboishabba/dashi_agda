#!/usr/bin/env python3
"""Finite reduced-word regression for three-root Alexander horn substitutions.

This is a bounded combinatorial test, not certification of wild embedding,
van Kampen, the infinite colimit, or an Agda kernel theorem.
"""
from itertools import product

def reduce_word(word):
    reduced = []
    for gen, sign in word:
        if reduced and reduced[-1] == (gen, -sign):
            reduced.pop()
        else:
            reduced.append((gen, sign))
    return tuple(reduced)

def inverse(word):
    return tuple((g, -sgn) for g, sgn in reversed(word))

def multiply(*words):
    return reduce_word(letter for word in words for letter in word)

def generator(sector, address=()):
    return (((sector, tuple(address)), 1),)

def commutator(a, b):
    return multiply(a, b, inverse(a), inverse(b))

def expand(word):
    result = ()
    for ((sector, addr), sign) in word:
        q = commutator(generator(sector, addr + (0,)),
                       generator(sector, addr + (1,)))
        result = multiply(result, q if sign == 1 else inverse(q))
    return result

def rotate(word):
    return tuple((((sector + 1) % 3, addr), sign)
                 for ((sector, addr), sign) in word)

def project(word, sector=0):
    return reduce_word((g, sign) for g, sign in word if g[0] == sector)

def all_reduced_words(max_len=4):
    alphabet = tuple(((i, ()), s) for i in range(3) for s in (-1, 1))
    yield ()
    for n in range(1, max_len + 1):
        for letters in product(alphabet, repeat=n):
            w = reduce_word(letters)
            if len(w) == n:
                yield w

def run():
    count = 0
    for word in all_reduced_words(4):
        count += 1
        assert reduce_word(word) == word
        assert rotate(rotate(rotate(word))) == word
        assert rotate(expand(word)) == expand(rotate(word))
        assert (not expand(word)) == (not word)
        assert (not expand(expand(word))) == (not word)
        assert project(multiply(word, inverse(word))) == ()
        if all(gen[0] == 0 for gen, _ in word):
            assert project(rotate(word)) == ()
    target = generator(0)
    assert project(target) != ()
    assert project(rotate(target)) == ()
    conjugators = 0
    for h in all_reduced_words(4):
        conjugators += 1
        inner_image = multiply(h, target, inverse(h))
        assert project(inner_image) != ()
        assert project(inner_image) != project(rotate(target))
    print('finite free words audited:', count)
    print('bounded conjugators excluded from implementing C3 rotation:', conjugators)
    print('binary expansions preserve C3 rotation and bounded nontriviality: PASS')
    print('first-sector retraction outer-obstruction: PASS (bounded regression)')
    print('general outer proof: group-theoretic argument; geometry/kernel: NOT CERTIFIED')

if __name__ == '__main__':
    run()
