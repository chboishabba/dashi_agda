#!/usr/bin/env python3
"""Exact 3B finite Weyl intertwiner recovery; NOT actual Monster matrices.

Owners: DASHI/Moonshine/Monster3BFiniteHeisenbergGeneratorsExact.agda
and Monster3BMultiplicityEvaluationExact.agda.
"""
import argparse
import json
import random
from fractions import Fraction

Q = 3
N = Q ** 6
M = 90
SIZE = N * M

def coords(n):
    return tuple((n // Q ** k) % Q for k in range(6))

def step(n, axis):
    return n + (Q ** axis) * (1 if (n // Q ** axis) % Q < 2 else -2)

def verify():
    rng = random.Random(20261108)
    # Obscure ALL canonical source labels, not just the position index.
    perm = list(range(SIZE))
    rng.shuffle(perm)
    pos = [0] * SIZE
    phase = [0] * SIZE
    for src, dest in enumerate(perm):
        pos[dest] = src // M
        phase[dest] = rng.randrange(3)

    inv = [0] * SIZE
    for src, dest in enumerate(perm):
        inv[dest] = src

    def translate(i, axis):
        src = inv[i]
        target = perm[step(src // M, axis) * M + src % M]
        return target, (phase[target] - phase[i]) % 3

    def modulate(i, axis):
        return coords(pos[i])[axis]

    origins = sorted(i for i in range(SIZE)
                     if all(modulate(i, a) == 0 for a in range(6)))
    assert len(origins) == M
    intertwiner = {}
    for k, origin in enumerate(origins):
        for x in range(N):
            target, amp = origin, 0
            for a, digit in enumerate(coords(x)):
                for _ in range(digit):
                    target, new = translate(target, a)
                    amp = (amp + new) % 3
            intertwiner[x, k] = target, amp
    assert len(set(i for i, _ in intertwiner.values())) == SIZE

    checks = 0
    for (x, k), (idx, amp) in intertwiner.items():
        for a in range(6):
            dest, delta = translate(idx, a)
            assert intertwiner[step(x, a), k] == (dest, (amp + delta) % 3)
            assert modulate(idx, a) == coords(x)[a]
            checks += 2
    assert checks == 787320

    # Two C3-equivalent unital rational algebras have different products.
    # coordinatewise: Aut = S3, no nonzero nilpotents;
    # square-zero radical: Aut = GL2(Q), infinite.
    def scalar(v):
        return sum(v, Fraction(0)) / 3
    def square_zero(v, w):
        s, t = scalar(v), scalar(w)
        return tuple(s * b + t * a - s * t for a, b in zip(v, w))
    u = (Fraction(1), Fraction(-1), Fraction(0))
    assert square_zero(u, u) == (0, 0, 0)
    assert tuple(a * a for a in u) != (0, 0, 0)
    for s in (Fraction(2), Fraction(3), Fraction(5, 2)):
        def auto(v):
            a = scalar(v)
            return tuple(a + s * (x - a) for x in v)
        for v in ((0, 1, 1), (1, -1, 0), (2, -1, 4)):
            for w in ((1, 1, 1), (0, 1, -1)):
                assert auto(square_zero(v, w)) == square_zero(auto(v), auto(w))

    return {
        "classification": "model only; no actual Monster 3B matrices",
        "heisenberg_basis": N,
        "multiplicity": M,
        "total_dimension": SIZE,
        "recovered_joint_zero_weight_basis": len(origins),
        "recovered_tensor_basis": len(intertwiner),
        "exact_12_generator_intertwining_checks": checks,
        "same_C3_action_does_not_determine_Griess_product": True,
        "actual_Monster_3B_intertwiner_obtained": False,
        "actual_Griess_product_verified": False,
        "VOA_automorphism_identification_obtained": False,
    }

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json")
    args = parser.parse_args()
    result = verify()
    print(json.dumps(result, indent=2))
    if args.json:
        with open(args.json, "w", encoding="utf-8") as fp:
            json.dump(result, fp, indent=2)
