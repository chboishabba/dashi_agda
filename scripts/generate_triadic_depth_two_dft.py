#!/usr/bin/env python3
"""Generate the exact depth-two cyclotomic DFT over Q(zeta_9).

The scalar module uses the basis 1,z,...,z^5 with z^6+z^3+1=0.
All proofs are exact rational ring-normalisation proofs; no floating point or
analytic trigonometric assumptions enter this finite theorem.

The emitted proofs target the standard-library 2.1 `Data.Rational.Solver`
interface used by the repository's focused Agda gate.  The Python side expands
only the finite polynomial syntax supplied to that trusted solver.
"""
from __future__ import annotations

import argparse
from pathlib import Path
from typing import TypeAlias

OUTPUT = Path("DASHI/Algebra/TriadicDepthTwoCyclotomicDFT.agda")

Expr: TypeAlias = tuple
C9Expr: TypeAlias = tuple[Expr, Expr, Expr, Expr, Expr, Expr]
SignalExpr: TypeAlias = list[C9Expr]


def variable(name: str) -> Expr:
    return ("var", name)


def constant(name: str) -> Expr:
    return ("con", name)


def plus(left: Expr, right: Expr) -> Expr:
    return ("plus", left, right)


def times(left: Expr, right: Expr) -> Expr:
    return ("times", left, right)


def negative(value: Expr) -> Expr:
    return ("neg", value)


def render(expression: Expr) -> str:
    tag = expression[0]
    if tag == "var":
        return expression[1]
    if tag == "con":
        return f"con {expression[1]}"
    if tag == "plus":
        return f"({render(expression[1])} :+ {render(expression[2])})"
    if tag == "times":
        return f"({render(expression[1])} :* {render(expression[2])})"
    if tag == "neg":
        return f"(:- {render(expression[1])})"
    raise ValueError(f"unknown expression: {expression!r}")


def solve_term(variables: list[str], left: Expr, right: Expr) -> str:
    binders = " ".join(variables)
    arguments = " ".join(variables)
    return (
        f"(solve {len(variables)} "
        f"(λ {binders} → {render(left)} := {render(right)}) "
        f"refl {arguments})"
    )


def c9_variables(prefix: str) -> C9Expr:
    return tuple(variable(f"{prefix}{coordinate}") for coordinate in range(6))  # type: ignore[return-value]


def zero_c9_expr() -> C9Expr:
    zero = constant("0ℚ")
    return zero, zero, zero, zero, zero, zero


def add_c9(left: C9Expr, right: C9Expr) -> C9Expr:
    return tuple(plus(a, b) for a, b in zip(left, right))  # type: ignore[return-value]


def scale_c9(scalar_name: str, value: C9Expr) -> C9Expr:
    scalar = constant(scalar_name)
    return tuple(times(scalar, coordinate) for coordinate in value)  # type: ignore[return-value]


def zeta_mul_expr(value: C9Expr) -> C9Expr:
    a0, a1, a2, a3, a4, a5 = value
    return (
        negative(a5),
        a0,
        a1,
        plus(a2, negative(a5)),
        a3,
        a4,
    )


def phase_expr(power: int, value: C9Expr) -> C9Expr:
    result = value
    for _ in range(power % 9):
        result = zeta_mul_expr(result)
    return result


def sum_c9(values: list[C9Expr]) -> C9Expr:
    assert values
    result = values[-1]
    for value in reversed(values[:-1]):
        result = add_c9(value, result)
    return result


def dot_c9(left: C9Expr, right: C9Expr) -> Expr:
    products = [times(a, b) for a, b in zip(left, right)]
    result = products[-1]
    for product in reversed(products[:-1]):
        result = plus(product, result)
    return result


def sum_q(values: list[Expr]) -> Expr:
    assert values
    result = values[-1]
    for value in reversed(values[:-1]):
        result = plus(value, result)
    return result


def invariant_pair_expr(left: C9Expr, right: C9Expr) -> Expr:
    return sum_q(
        [dot_c9(phase_expr(k, left), phase_expr(k, right)) for k in range(9)]
    )


def analyze_expr(signal: SignalExpr) -> SignalExpr:
    return [
        sum_c9(
            [phase_expr((-m * x) % 9, signal[x]) for x in range(9)]
        )
        for m in range(9)
    ]


def synthesize_expr(spectrum: SignalExpr) -> SignalExpr:
    return [
        scale_c9(
            "oneNinth",
            sum_c9(
                [phase_expr((m * x) % 9, spectrum[m]) for m in range(9)]
            ),
        )
        for x in range(9)
    ]


def signal_energy_expr(signal: SignalExpr) -> Expr:
    return sum_q([invariant_pair_expr(value, value) for value in signal])


def vars_for(prefixes: list[str]) -> list[str]:
    return [f"{prefix}{coordinate}" for prefix in prefixes for coordinate in range(6)]


def c9_pattern(prefix: str) -> str:
    return "(c9 " + " ".join(f"{prefix}{k}" for k in range(6)) + ")"


def generate() -> str:
    lines: list[str] = [
        "module DASHI.Algebra.TriadicDepthTwoCyclotomicDFT where",
        "",
        "open import Agda.Builtin.Equality using (_≡_; refl)",
        "open import Agda.Builtin.Nat using (Nat; zero; suc)",
        "open import Agda.Builtin.String using (String)",
        "open import Data.Integer using (+_)",
        "open import Data.List.Base using ([]; _∷_)",
        "open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)",
        "open import Data.Rational.Solver using (module +-*-Solver)",
        "open +-*-Solver",
        "",
        "open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope",
        "  using (neg; zer; pos; []; _∷_)",
        "",
        "import DASHI.Foundations.TriadicFiniteQuotient as Q",
        "import DASHI.Algebra.TriadicFiniteIrrep as Irrep",
        "",
        "------------------------------------------------------------------------",
        "-- Nine cyclic indices and exact modular arithmetic tables.",
        "",
        "data Index9 : Set where",
        "  i0 i1 i2 i3 i4 i5 i6 i7 i8 : Index9",
        "",
        "addIndex : Index9 → Index9 → Index9",
    ]
    for a in range(9):
        for b in range(9):
            lines.append(f"addIndex i{a} i{b} = i{(a + b) % 9}")
    lines.extend(["", "mulIndex : Index9 → Index9 → Index9"])
    for a in range(9):
        for b in range(9):
            lines.append(f"mulIndex i{a} i{b} = i{(a * b) % 9}")
    lines.extend(["", "negIndex : Index9 → Index9"])
    for a in range(9):
        lines.append(f"negIndex i{a} = i{(-a) % 9}")

    lines.extend(
        [
            "",
            "addIndexAssociative :",
            "  (a b c : Index9) →",
            "  addIndex (addIndex a b) c ≡ addIndex a (addIndex b c)",
        ]
    )
    for a in range(9):
        for b in range(9):
            for c in range(9):
                lines.append(f"addIndexAssociative i{a} i{b} i{c} = refl")

    lines.extend(
        [
            "",
            "addIndexCommutative :",
            "  (a b : Index9) → addIndex a b ≡ addIndex b a",
        ]
    )
    for a in range(9):
        for b in range(9):
            lines.append(f"addIndexCommutative i{a} i{b} = refl")

    lines.extend(
        [
            "",
            "mulDistributesOverAdd :",
            "  (m x y : Index9) →",
            "  mulIndex m (addIndex x y)",
            "  ≡ addIndex (mulIndex m x) (mulIndex m y)",
        ]
    )
    for m in range(9):
        for x in range(9):
            for y in range(9):
                lines.append(f"mulDistributesOverAdd i{m} i{x} i{y} = refl")

    lines.extend(
        [
            "",
            "------------------------------------------------------------------------",
            "-- The exact six-dimensional Q(zeta_9) coefficient module.",
            "",
            "record C9 : Set where",
            "  constructor c9",
            "  field",
            "    c0 c1 c2 c3 c4 c5 : ℚ",
            "",
            "open C9 public",
            "",
            "c9-ext :",
            "  ∀ {a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : ℚ} →",
            "  a0 ≡ b0 → a1 ≡ b1 → a2 ≡ b2 →",
            "  a3 ≡ b3 → a4 ≡ b4 → a5 ≡ b5 →",
            "  c9 a0 a1 a2 a3 a4 a5 ≡ c9 b0 b1 b2 b3 b4 b5",
            "c9-ext refl refl refl refl refl refl = refl",
            "",
            "zeroC9 : C9",
            "zeroC9 = c9 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ",
            "",
            "addC9 : C9 → C9 → C9",
            "addC9 (c9 a0 a1 a2 a3 a4 a5) (c9 b0 b1 b2 b3 b4 b5) =",
            "  c9 (a0 + b0) (a1 + b1) (a2 + b2)",
            "     (a3 + b3) (a4 + b4) (a5 + b5)",
            "",
            "negateC9 : C9 → C9",
            "negateC9 (c9 a0 a1 a2 a3 a4 a5) =",
            "  c9 (- a0) (- a1) (- a2) (- a3) (- a4) (- a5)",
            "",
            "scaleC9 : ℚ → C9 → C9",
            "scaleC9 q (c9 a0 a1 a2 a3 a4 a5) =",
            "  c9 (q * a0) (q * a1) (q * a2)",
            "     (q * a3) (q * a4) (q * a5)",
            "",
            "-- Multiplication by zeta_9, reduced by zeta^6 = -zeta^3 - 1.",
            "zetaMul : C9 → C9",
            "zetaMul (c9 a0 a1 a2 a3 a4 a5) =",
            "  c9 (- a5) a0 a1 (a2 + (- a5)) a3 a4",
            "",
            "phaseMul : Index9 → C9 → C9",
            "phaseMul i0 a = a",
        ]
    )
    for k in range(1, 9):
        nested = "a"
        for _ in range(k):
            nested = f"zetaMul ({nested})"
        lines.append(f"phaseMul i{k} a = {nested}")

    phase_names = [f"a{k}" for k in range(6)]
    phase_value = c9_variables("a")
    lines.extend(
        [
            "",
            "phaseActionLaw :",
            "  (a b : Index9) →",
            "  (x : C9) →",
            "  phaseMul (addIndex a b) x ≡ phaseMul a (phaseMul b x)",
        ]
    )
    for a in range(9):
        for b in range(9):
            left = phase_expr((a + b) % 9, phase_value)
            right = phase_expr(a, phase_expr(b, phase_value))
            lines.extend(
                [
                    f"phaseActionLaw i{a} i{b} (c9 {' '.join(phase_names)}) =",
                    "  c9-ext",
                ]
            )
            for left_coordinate, right_coordinate in zip(left, right):
                lines.append(
                    f"    {solve_term(phase_names, left_coordinate, right_coordinate)}"
                )

    cyclotomic_left = add_c9(
        phase_expr(6, phase_value),
        add_c9(phase_expr(3, phase_value), phase_value),
    )
    lines.extend(
        [
            "",
            "cyclotomicRelation :",
            "  (x : C9) →",
            "  addC9 (phaseMul i6 x) (addC9 (phaseMul i3 x) x) ≡ zeroC9",
            f"cyclotomicRelation (c9 {' '.join(phase_names)}) =",
            "  c9-ext",
        ]
    )
    for coordinate in cyclotomic_left:
        lines.append(
            f"    {solve_term(phase_names, coordinate, constant('0ℚ'))}"
        )

    lines.extend(
        [
            "",
            "------------------------------------------------------------------------",
            "-- Exact identification with the balanced-ternary depth-two quotient.",
            "",
            "indexToResidue : Index9 → Q.Residue3Pow Q.two",
            "indexToResidue i0 = zer ∷ zer ∷ []",
            "indexToResidue i1 = pos ∷ zer ∷ []",
            "indexToResidue i2 = neg ∷ zer ∷ []",
            "indexToResidue i3 = zer ∷ pos ∷ []",
            "indexToResidue i4 = pos ∷ pos ∷ []",
            "indexToResidue i5 = neg ∷ pos ∷ []",
            "indexToResidue i6 = zer ∷ neg ∷ []",
            "indexToResidue i7 = pos ∷ neg ∷ []",
            "indexToResidue i8 = neg ∷ neg ∷ []",
            "",
            "residueToIndex : Q.Residue3Pow Q.two → Index9",
            "residueToIndex (zer ∷ zer ∷ []) = i0",
            "residueToIndex (pos ∷ zer ∷ []) = i1",
            "residueToIndex (neg ∷ zer ∷ []) = i2",
            "residueToIndex (zer ∷ pos ∷ []) = i3",
            "residueToIndex (pos ∷ pos ∷ []) = i4",
            "residueToIndex (neg ∷ pos ∷ []) = i5",
            "residueToIndex (zer ∷ neg ∷ []) = i6",
            "residueToIndex (pos ∷ neg ∷ []) = i7",
            "residueToIndex (neg ∷ neg ∷ []) = i8",
            "",
            "indexRoundTrip : (i : Index9) → residueToIndex (indexToResidue i) ≡ i",
        ]
    )
    for k in range(9):
        lines.append(f"indexRoundTrip i{k} = refl")
    lines.extend(
        [
            "",
            "residueRoundTrip :",
            "  (r : Q.Residue3Pow Q.two) → indexToResidue (residueToIndex r) ≡ r",
            "residueRoundTrip (zer ∷ zer ∷ []) = refl",
            "residueRoundTrip (pos ∷ zer ∷ []) = refl",
            "residueRoundTrip (neg ∷ zer ∷ []) = refl",
            "residueRoundTrip (zer ∷ pos ∷ []) = refl",
            "residueRoundTrip (pos ∷ pos ∷ []) = refl",
            "residueRoundTrip (neg ∷ pos ∷ []) = refl",
            "residueRoundTrip (zer ∷ neg ∷ []) = refl",
            "residueRoundTrip (pos ∷ neg ∷ []) = refl",
            "residueRoundTrip (neg ∷ neg ∷ []) = refl",
            "",
            "------------------------------------------------------------------------",
            "-- Nine-component signal carrier and finite sums.",
            "",
            "record Signal9 : Set where",
            "  constructor signal9",
            "  field",
            "    v0 v1 v2 v3 v4 v5 v6 v7 v8 : C9",
            "",
            "open Signal9 public",
            "",
            "atSignal : Signal9 → Index9 → C9",
        ]
    )
    for k in range(9):
        lines.append(f"atSignal s i{k} = v{k} s")
    lines.extend(
        [
            "",
            "sum9C9 : C9 → C9 → C9 → C9 → C9 → C9 → C9 → C9 → C9 → C9",
            "sum9C9 a b c d e f g h i =",
            "  addC9 a (addC9 b (addC9 c (addC9 d (addC9 e (addC9 f (addC9 g (addC9 h i)))))))",
            "",
            "sum9Q : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ",
            "sum9Q a b c d e f g h i =",
            "  a + (b + (c + (d + (e + (f + (g + (h + i)))))))",
            "",
            "oneNinth : ℚ",
            "oneNinth = + 1 / 9",
            "",
            "nineQ : ℚ",
            "nineQ = + 9 / 1",
            "",
            "characterAction : Index9 → Index9 → C9 → C9",
            "characterAction frequency point =",
            "  phaseMul (mulIndex frequency point)",
            "",
            "characterAdditive :",
            "  (frequency x y : Index9) →",
            "  (a : C9) →",
            "  characterAction frequency (addIndex x y) a",
            "  ≡ characterAction frequency x (characterAction frequency y a)",
            "characterAdditive frequency x y a",
            "  rewrite mulDistributesOverAdd frequency x y",
            "        | phaseActionLaw (mulIndex frequency x) (mulIndex frequency y) a = refl",
            "",
            "analyzeAt : Signal9 → Index9 → C9",
            "analyzeAt f m =",
            "  sum9C9",
        ]
    )
    for x in range(9):
        lines.append(
            f"    (phaseMul (negIndex (mulIndex m i{x})) (atSignal f i{x}))"
        )
    lines.extend(
        [
            "",
            "analyze9 : Signal9 → Signal9",
            "analyze9 f = signal9",
        ]
    )
    for m in range(9):
        lines.append(f"    (analyzeAt f i{m})")
    lines.extend(
        [
            "",
            "synthesizeAt : Signal9 → Index9 → C9",
            "synthesizeAt spectrum x =",
            "  scaleC9 oneNinth",
            "    (sum9C9",
        ]
    )
    for m in range(9):
        lines.append(
            f"      (phaseMul (mulIndex i{m} x) (atSignal spectrum i{m}))"
        )
    lines.append("    )")
    lines.extend(
        [
            "",
            "synthesize9 : Signal9 → Signal9",
            "synthesize9 spectrum = signal9",
        ]
    )
    for x in range(9):
        lines.append(f"    (synthesizeAt spectrum i{x})")

    prefixes = [f"a{k}" for k in range(9)]
    variables = vars_for(prefixes)
    symbolic_signal = [c9_variables(prefix) for prefix in prefixes]
    reconstructed = synthesize_expr(analyze_expr(symbolic_signal))
    pattern = "signal9\n    " + "\n    ".join(c9_pattern(prefix) for prefix in prefixes)
    lines.extend(
        [
            "",
            "reconstructAnalyze9 :",
            "  (f : Signal9) →",
            "  (x : Index9) →",
            "  atSignal (synthesize9 (analyze9 f)) x ≡ atSignal f x",
        ]
    )
    for x in range(9):
        lines.extend(
            [
                f"reconstructAnalyze9 ({pattern}) i{x} =",
                "  c9-ext",
            ]
        )
        for left_coordinate, right_coordinate in zip(
            reconstructed[x], symbolic_signal[x]
        ):
            lines.append(
                f"    {solve_term(variables, left_coordinate, right_coordinate)}"
            )

    lines.extend(
        [
            "",
            "------------------------------------------------------------------------",
            "-- Character orthogonality as an operator identity.",
            "",
            "characterSum : Index9 → C9 → C9",
            "characterSum difference a =",
            "  sum9C9",
        ]
    )
    for m in range(9):
        lines.append(f"    (phaseMul (mulIndex i{m} difference) a)")
    lines.extend(
        [
            "",
            "orthogonalityTarget : Index9 → C9 → C9",
            "orthogonalityTarget i0 a = scaleC9 nineQ a",
        ]
    )
    for k in range(1, 9):
        lines.append(f"orthogonalityTarget i{k} a = zeroC9")
    lines.extend(
        [
            "",
            "characterOrthogonality9 :",
            "  (difference : Index9) →",
            "  (a : C9) →",
            "  characterSum difference a ≡ orthogonalityTarget difference a",
        ]
    )
    for difference in range(9):
        left = sum_c9(
            [phase_expr((m * difference) % 9, phase_value) for m in range(9)]
        )
        right = scale_c9("nineQ", phase_value) if difference == 0 else zero_c9_expr()
        lines.extend(
            [
                f"characterOrthogonality9 i{difference} (c9 {' '.join(phase_names)}) =",
                "  c9-ext",
            ]
        )
        for left_coordinate, right_coordinate in zip(left, right):
            lines.append(
                f"    {solve_term(phase_names, left_coordinate, right_coordinate)}"
            )

    lines.extend(
        [
            "",
            "------------------------------------------------------------------------",
            "-- A phase-invariant rational Hermitian form and Parseval theorem.",
            "",
            "dotC9 : C9 → C9 → ℚ",
            "dotC9 (c9 a0 a1 a2 a3 a4 a5) (c9 b0 b1 b2 b3 b4 b5) =",
            "  a0 * b0 + (a1 * b1 + (a2 * b2 + (a3 * b3 + (a4 * b4 + a5 * b5))))",
            "",
            "invariantPair : C9 → C9 → ℚ",
            "invariantPair a b =",
            "  sum9Q",
        ]
    )
    for k in range(9):
        lines.append(f"    (dotC9 (phaseMul i{k} a) (phaseMul i{k} b))")
    lines.extend(
        [
            "",
            "signalEnergy : Signal9 → ℚ",
            "signalEnergy f =",
            "  sum9Q",
        ]
    )
    for k in range(9):
        lines.append(f"    (invariantPair (atSignal f i{k}) (atSignal f i{k}))")

    parseval_left = signal_energy_expr(analyze_expr(symbolic_signal))
    parseval_right = times(constant("nineQ"), signal_energy_expr(symbolic_signal))
    lines.extend(
        [
            "",
            "parseval9 :",
            "  (f : Signal9) →",
            "  signalEnergy (analyze9 f) ≡ nineQ * signalEnergy f",
            f"parseval9 ({pattern}) =",
            f"  {solve_term(variables, parseval_left, parseval_right)}",
            "",
            "------------------------------------------------------------------------",
            "-- Existing exact-codec integration at depth two.",
            "",
            "packSignal : Irrep.Signal Q.two C9 → Signal9",
            "packSignal f = signal9",
        ]
    )
    for k in range(9):
        lines.append(f"    (f (indexToResidue i{k}))")
    lines.extend(
        [
            "",
            "unpackSignal : Signal9 → Irrep.Signal Q.two C9",
            "unpackSignal f residue = atSignal f (residueToIndex residue)",
            "",
            "depthTwoCyclotomicCodec : Irrep.ExactSpectralCodec Q.two",
            "depthTwoCyclotomicCodec =",
            "  record",
            "    { Coeff = C9",
            "    ; Spectrum = Signal9",
            "    ; analyze = λ f → analyze9 (packSignal f)",
            "    ; synthesize = λ spectrum → unpackSignal (synthesize9 spectrum)",
            "    ; reconstructAnalyze = reconstruct",
            "    ; spectralWidth = Q.pow3 Q.two",
            "    ; spectralWidthMatchesQuotient = refl",
            "    }",
            "  where",
            "  reconstruct :",
            "    (f : Irrep.Signal Q.two C9) →",
            "    (r : Q.Residue3Pow Q.two) →",
            "    unpackSignal (synthesize9 (analyze9 (packSignal f))) r ≡ f r",
            "  reconstruct f (zer ∷ zer ∷ []) = reconstructAnalyze9 (packSignal f) i0",
            "  reconstruct f (pos ∷ zer ∷ []) = reconstructAnalyze9 (packSignal f) i1",
            "  reconstruct f (neg ∷ zer ∷ []) = reconstructAnalyze9 (packSignal f) i2",
            "  reconstruct f (zer ∷ pos ∷ []) = reconstructAnalyze9 (packSignal f) i3",
            "  reconstruct f (pos ∷ pos ∷ []) = reconstructAnalyze9 (packSignal f) i4",
            "  reconstruct f (neg ∷ pos ∷ []) = reconstructAnalyze9 (packSignal f) i5",
            "  reconstruct f (zer ∷ neg ∷ []) = reconstructAnalyze9 (packSignal f) i6",
            "  reconstruct f (pos ∷ neg ∷ []) = reconstructAnalyze9 (packSignal f) i7",
            "  reconstruct f (neg ∷ neg ∷ []) = reconstructAnalyze9 (packSignal f) i8",
            "",
            "dftStatement : String",
            "dftStatement =",
            '  "The depth-two quotient Z/9Z has an exact nine-point cyclotomic DFT over Q(zeta_9), with the Phi_9 relation, additive character action, complete operator orthogonality, pointwise inverse transform, and rational Hermitian Parseval identity checked by normalization."',
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
