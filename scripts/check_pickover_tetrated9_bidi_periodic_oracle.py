#!/usr/bin/env python3
"""Finite exact fast jump for RATIONAL phase seeds, not 1/(2*pi).

DASHI donors: SelfIndexingHyperfabricTetrationExact (A[n+1]=9**A[n]),
SelfIndexedParetoHyperfabricTetrationExact, TypedHyperfabricPantsGluingBridgeExact,
ActiveBidiDiscriminatorLoopExact, ShorReversiblePowModOracleWeldExact.

Nonarchimedean/finite producer uses a certified multiplicative period of
99 modulo q. It never expands 9999! or 99**(9999!).
"""
from dataclasses import dataclass
from math import factorial, gcd

BASE = 99
N = 9999


@dataclass(frozen=True)
class NineSelfIndexingAddress:
    # Lazy DESCRIPTION of tower width, not a level-n function producer.
    level: int

    def width_expression(self):
        return "1" if self.level == 0 else f"9^^{self.level}"


@dataclass(frozen=True)
class RationalPhaseWitness:
    numerator: int
    denominator: int
    period: int

    def valid(self):
        return (
            self.denominator > 1 and self.period > 0
            and gcd(BASE, self.denominator) == 1
            and pow(BASE, self.period, self.denominator) == 1
        )


def factorial_mod(n, modulus):
    assert modulus > 0
    r = 1 % modulus
    for k in range(2, n + 1):
        r = r * k % modulus
    return r


def direct_oracle(w, n):
    assert w.valid()
    return w.numerator * pow(BASE, factorial(n), w.denominator) % w.denominator


def compressed_oracle(w, n):
    assert w.valid()
    reduced = factorial_mod(n, w.period)
    residue = w.numerator * pow(BASE, reduced, w.denominator) % w.denominator
    return residue, reduced


def sine_sign_residue(residue, q):
    assert 0 <= residue < q
    return 0 if 2 * residue in (0, q) else (1 if 2 * residue < q else -1)


def bidi_collision(w, n, depth):
    """Two same-cell rational seeds with opposite terminal signs."""
    multiplier = pow(BASE, factorial_mod(n, w.period), w.denominator)
    groups = {}
    for a in range(1, w.denominator):
        cell = (a * 3**depth) // w.denominator
        outcome = sine_sign_residue(a * multiplier % w.denominator, w.denominator)
        if outcome == 0:
            continue
        old = groups.setdefault(cell, {})
        if -outcome in old:
            b = old[-outcome]
            assert (b * 3**depth) // w.denominator == cell
            return b, a, cell, (-outcome, outcome)
        old.setdefault(outcome, a)
    return None


def main():
    cases = (
        RationalPhaseWitness(1, 101, 100),
        RationalPhaseWitness(1, 20123, 20122),
        RationalPhaseWitness(1, 20183, 20182),
        RationalPhaseWitness(100, 200, 80),
        RationalPhaseWitness(99, 200, 80),
        RationalPhaseWitness(101, 200, 80),
    )
    for witness in cases:
        assert witness.valid(), witness
        for n in range(1, 9):
            assert compressed_oracle(witness, n)[0] == direct_oracle(witness, n)
        residue, reduced = compressed_oracle(witness, N)
        sign = sine_sign_residue(residue, witness.denominator)
        print(f"CERT q={witness.denominator} a={witness.numerator} "
              f"period={witness.period} E_mod_period={reduced} "
              f"residue={residue} sign={sign}")

    assert compressed_oracle(cases[1], N) == (18371, 5752)
    assert compressed_oracle(cases[2], N) == (2114, 4834)
    assert sine_sign_residue(compressed_oracle(cases[3], N)[0], 200) == 0
    assert sine_sign_residue(compressed_oracle(cases[4], N)[0], 200) == +1
    assert sine_sign_residue(compressed_oracle(cases[5], N)[0], 200) == -1

    for depth in (1, 2, 3, 4, 5):
        pair = bidi_collision(cases[1], N, depth)
        assert pair is not None, depth
        a, b, cell, signs = pair
        print(f"BIDI depth={depth}: a={a}, b={b}, "
              f"shared cell={cell}, terminal signs={signs}")

    assert NineSelfIndexingAddress(9).width_expression() == "9^^9"
    print("PASS exact 9999! rational-period sign without expanding exponent")
    print("PASS BIDI collisions at 3/9/27/81/243 coarse resolutions")
    print("OPEN actual irrational 1/(2*pi): no certified finite period")


if __name__ == "__main__":
    main()
