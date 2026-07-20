#!/usr/bin/env python3
"""Generate the exhaustive arbitrary-depth balanced-ternary arithmetic proof.

The only exhaustive part is the finite local carry automaton.  The generated
Agda theorem then closes by structural recursion on the retained depth.
"""
from __future__ import annotations

import argparse
from itertools import product
from pathlib import Path

OUTPUT = Path("DASHI/Algebra/TriadicFiniteArithmeticLaws.agda")
TRITS = (-1, 0, 1)
NAME = {-1: "neg", 0: "zer", 1: "pos"}
CHAR = {-1: "m", 0: "z", 1: "p"}


def add_pair(x: int, y: int) -> tuple[int, int]:
    return {
        -2: (1, -1),
        -1: (-1, 0),
        0: (0, 0),
        1: (1, 0),
        2: (-1, 1),
    }[x + y]


def merge_carry(first: int, second: int) -> int:
    return {
        (-1, -1): -1,
        (-1, 0): -1,
        (-1, 1): 0,
        (0, -1): -1,
        (0, 0): 0,
        (0, 1): 1,
        (1, -1): 0,
        (1, 0): 1,
        (1, 1): 1,
    }[(first, second)]


def full_add(carry: int, x: int, y: int) -> tuple[int, int]:
    digit, first = add_pair(x, y)
    output, second = add_pair(digit, carry)
    result = output, merge_carry(first, second)
    assert result[0] + 3 * result[1] == carry + x + y
    return result


def balance_name(values: tuple[int, int, int, int]) -> str:
    return "bal-" + "".join(CHAR[value] for value in values)


def generate() -> str:
    balances = [
        values
        for values in product(TRITS, repeat=4)
        if values[0] + values[1] == values[2] + values[3]
    ]
    assert len(balances) == 19
    balance_names = {values: balance_name(values) for values in balances}

    lines: list[str] = [
        "module DASHI.Algebra.TriadicFiniteArithmeticLaws where",
        "",
        "open import Agda.Builtin.Equality using (_≡_; refl)",
        "open import Agda.Builtin.Nat using (Nat)",
        "open import Agda.Builtin.String using (String)",
        "",
        "open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope",
        "  using (Trit; neg; zer; pos; []; _∷_)",
        "",
        "import DASHI.Foundations.TriadicFiniteQuotient as Q",
        "import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic",
        "import DASHI.Algebra.TriadicFiniteIrrep as Irrep",
        "",
        "------------------------------------------------------------------------",
        "-- Generated finite carry-balance relation.",
        "",
        "data CarryBalance : Trit → Trit → Trit → Trit → Set where",
    ]
    for values in balances:
        indices = " ".join(NAME[value] for value in values)
        lines.append(f"  {balance_names[values]} : CarryBalance {indices}")

    lines.extend(
        [
            "",
            "------------------------------------------------------------------------",
            "-- Commutativity for every incoming carry and every depth.",
            "",
            "commuteWithCarry :",
            "  ∀ {n : Nat} →",
            "  (carry : Trit) →",
            "  (x y : Q.Residue3Pow n) →",
            "  Arithmetic.addWithCarry carry x y",
            "  ≡ Arithmetic.addWithCarry carry y x",
            "commuteWithCarry carry [] [] = refl",
        ]
    )
    for carry, x, y in product(TRITS, repeat=3):
        _, next_carry = full_add(carry, x, y)
        lines.extend(
            [
                f"commuteWithCarry {NAME[carry]} ({NAME[x]} ∷ xs) ({NAME[y]} ∷ ys)",
                f"  rewrite commuteWithCarry {NAME[next_carry]} xs ys = refl",
            ]
        )

    lines.extend(
        [
            "",
            "------------------------------------------------------------------------",
            "-- General carry-balanced associativity.",
            "",
            "associateWithCarries :",
            "  ∀ {n : Nat} {a b c d : Trit} →",
            "  CarryBalance a b c d →",
            "  (x y z : Q.Residue3Pow n) →",
            "  Arithmetic.addWithCarry a (Arithmetic.addWithCarry b x y) z",
            "  ≡ Arithmetic.addWithCarry c x (Arithmetic.addWithCarry d y z)",
            "associateWithCarries balance [] [] [] = refl",
        ]
    )
    for balance in balances:
        a, b, c, d = balance
        for x, y, z in product(TRITS, repeat=3):
            left_digit, left_inner = full_add(b, x, y)
            left_output, left_outer = full_add(a, left_digit, z)
            right_digit, right_inner = full_add(d, y, z)
            right_output, right_outer = full_add(c, x, right_digit)
            assert left_output == right_output
            next_balance = (left_outer, left_inner, right_outer, right_inner)
            assert next_balance in balance_names
            lines.extend(
                [
                    f"associateWithCarries {balance_names[balance]} "
                    f"({NAME[x]} ∷ xs) ({NAME[y]} ∷ ys) ({NAME[z]} ∷ zs)",
                    f"  rewrite associateWithCarries {balance_names[next_balance]} xs ys zs = refl",
                ]
            )

    lines.extend(
        [
            "",
            "------------------------------------------------------------------------",
            "-- Public arbitrary-depth laws.",
            "",
            "commutativeAllDepth :",
            "  ∀ {n : Nat} →",
            "  (x y : Q.Residue3Pow n) →",
            "  Arithmetic.addResidue x y ≡ Arithmetic.addResidue y x",
            "commutativeAllDepth = commuteWithCarry zer",
            "",
            "associativeAllDepth :",
            "  ∀ {n : Nat} →",
            "  (x y z : Q.Residue3Pow n) →",
            "  Arithmetic.addResidue (Arithmetic.addResidue x y) z",
            "  ≡ Arithmetic.addResidue x (Arithmetic.addResidue y z)",
            "associativeAllDepth = associateWithCarries bal-zzzz",
            "",
            "open Arithmetic.TriadicArithmeticLawReceipt",
            "",
            "allDepthArithmeticLaws :",
            "  (n : Nat) →",
            "  Arithmetic.TriadicArithmeticLawReceipt n",
            "allDepthArithmeticLaws n =",
            "  record",
            "    { associativity = associativeAllDepth",
            "    ; commutative = commutativeAllDepth",
            "    }",
            "",
            "finiteAdditiveGroupAllDepth :",
            "  (n : Nat) →",
            "  Irrep.FiniteAdditiveGroup n",
            "finiteAdditiveGroupAllDepth n =",
            "  Arithmetic.finiteAdditiveGroup n (allDepthArithmeticLaws n)",
            "",
            "arithmeticLawsStatement : String",
            "arithmeticLawsStatement =",
            '  "The ripple-carry balanced-ternary operation is associative and commutative at every finite depth; the proof is a carry-balance bisimulation whose complete finite local transition table is checked definitionally."',
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    generated = generate()
    if args.check:
        current = OUTPUT.read_text(encoding="utf-8") if OUTPUT.exists() else ""
        if current != generated:
            raise SystemExit(f"{OUTPUT} is stale; run {Path(__file__).name}")
        return
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(generated, encoding="utf-8")


if __name__ == "__main__":
    main()
