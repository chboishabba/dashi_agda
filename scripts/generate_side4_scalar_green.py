#!/usr/bin/env python3
"""Generate an exact Agda Green-kernel certificate for the side-four torus.

The configured identity-background gauge-fixed operator reduces componentwise to

    - sum_mu backward_mu forward_mu + P_zero,

where P_zero is the normalized constant-mode projection.  On (Z/4Z)^4 the
Fourier eigenvalues of the Laplacian are sums of 0, 2, 4, 2, so the inverse
kernel is rational.  This generator performs every computation with
fractions.Fraction, verifies the local inverse equation and normalization, and
emits an Agda table whose 256 equations are discharged by the rational ring
solver.  No floating-point arithmetic or tolerance is used.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from pathlib import Path
import argparse
import hashlib

Point = tuple[int, int, int, int]
POINTS: tuple[Point, ...] = tuple(product(range(4), repeat=4))
ONE_DIMENSIONAL_LAPLACIAN = (0, 2, 4, 2)
REAL_I_POWER = (1, 0, -1, 0)


def real_character(momentum: Point, offset: Point) -> int:
    return REAL_I_POWER[sum(k * x for k, x in zip(momentum, offset)) % 4]


def inverse_eigenvalue(momentum: Point) -> Fraction:
    eigenvalue = sum(ONE_DIMENSIONAL_LAPLACIAN[k] for k in momentum)
    return Fraction(1, 1) if eigenvalue == 0 else Fraction(1, eigenvalue)


def green_kernel(offset: Point) -> Fraction:
    return sum(
        inverse_eigenvalue(momentum) * real_character(momentum, offset)
        for momentum in POINTS
    ) / 256


def shift(offset: Point, axis: int, amount: int) -> Point:
    result = list(offset)
    result[axis] = (result[axis] + amount) % 4
    return tuple(result)  # type: ignore[return-value]


def laplacian(kernel: dict[Point, Fraction], offset: Point) -> Fraction:
    return sum(
        2 * kernel[offset]
        - kernel[shift(offset, axis, 1)]
        - kernel[shift(offset, axis, -1)]
        for axis in range(4)
    )


def verify(kernel: dict[Point, Fraction]) -> None:
    if sum(kernel.values()) != 1:
        raise AssertionError("Green kernel does not have constant-mode mass one")

    for offset in POINTS:
        expected = Fraction(1 if offset == (0, 0, 0, 0) else 0, 1)
        actual = laplacian(kernel, offset) + Fraction(1, 256)
        if actual != expected:
            raise AssertionError(
                f"local inverse equation failed at {offset}: {actual} != {expected}"
            )


INDEX_PATTERN = {
    0: "zeroᵢ",
    1: "(sucᵢ zeroᵢ)",
    2: "(sucᵢ (sucᵢ zeroᵢ))",
    3: "(sucᵢ (sucᵢ (sucᵢ zeroᵢ)))",
}


def site_pattern(point: Point) -> str:
    x0, x1, x2, x3 = (INDEX_PATTERN[value] for value in point)
    return f"(pair (pair {x0} {x1}) (pair {x2} {x3}))"


def agda_rational(value: Fraction) -> str:
    if value == 0:
        return "0ℚ"
    if value == 1:
        return "1ℚ"
    if value > 0:
        return f"(+ {value.numerator} / {value.denominator})"
    return f"(- (+ {-value.numerator} / {value.denominator}))"


def render(kernel: dict[Point, Fraction]) -> str:
    kernel_clauses = "\n".join(
        f"scalarGreenKernel {site_pattern(point)} = {agda_rational(kernel[point])}"
        for point in POINTS
    )
    equation_clauses = "\n".join(
        f"scalarGreenKernelEquation {site_pattern(point)} = ℚRing.solve-∀"
        for point in POINTS
    )

    return f"""module DASHI.Physics.YangMills.BalabanSide4ScalarGreenKernelGenerated where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
  using (shiftForward4; shiftBackward4; siteSum4; siteSumAsCoordinates)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using (axis0; axis1; axis2; axis3)

oneTwoFiftySix : ℚ
oneTwoFiftySix = + 1 / 256

scalarGreenKernel : PhysicalBlockL side4 → ℚ
{kernel_clauses}

scalarKernelLaplacian : PhysicalBlockL side4 → ℚ
scalarKernelLaplacian offset =
  (scalarGreenKernel offset + scalarGreenKernel offset)
  - (scalarGreenKernel (shiftForward4 axis0 offset)
    + scalarGreenKernel (shiftBackward4 axis0 offset))
  + ((scalarGreenKernel offset + scalarGreenKernel offset)
    - (scalarGreenKernel (shiftForward4 axis1 offset)
      + scalarGreenKernel (shiftBackward4 axis1 offset)))
  + ((scalarGreenKernel offset + scalarGreenKernel offset)
    - (scalarGreenKernel (shiftForward4 axis2 offset)
      + scalarGreenKernel (shiftBackward4 axis2 offset)))
  + ((scalarGreenKernel offset + scalarGreenKernel offset)
    - (scalarGreenKernel (shiftForward4 axis3 offset)
      + scalarGreenKernel (shiftBackward4 axis3 offset)))

scalarDeltaAtZero : PhysicalBlockL side4 → ℚ
scalarDeltaAtZero (pair (pair zeroᵢ zeroᵢ) (pair zeroᵢ zeroᵢ)) = 1ℚ
scalarDeltaAtZero _ = 0ℚ

scalarGreenKernelEquation : ∀ offset →
  scalarKernelLaplacian offset + oneTwoFiftySix
  ≡ scalarDeltaAtZero offset
{equation_clauses}

scalarGreenKernelTotalExact : siteSum4 scalarGreenKernel ≡ 1ℚ
scalarGreenKernelTotalExact
  rewrite siteSumAsCoordinates scalarGreenKernel = ℚRing.solve-∀

scalarGreenKernelTableLevel : ProofLevel
scalarGreenKernelTableLevel = machineChecked

scalarGreenKernelEquationLevel : ProofLevel
scalarGreenKernelEquationLevel = machineChecked

scalarGreenKernelNormalizationLevel : ProofLevel
scalarGreenKernelNormalizationLevel = machineChecked
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(
            "DASHI/Physics/YangMills/"
            "BalabanSide4ScalarGreenKernelGenerated.agda"
        ),
    )
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args()

    kernel = {point: green_kernel(point) for point in POINTS}
    verify(kernel)
    rendered = render(kernel)

    if arguments.check:
        existing = arguments.output.read_text(encoding="utf-8")
        if existing != rendered:
            raise SystemExit(f"generated file is stale: {arguments.output}")
    else:
        arguments.output.parent.mkdir(parents=True, exist_ok=True)
        arguments.output.write_text(rendered, encoding="utf-8")

    digest = hashlib.sha256(rendered.encode("utf-8")).hexdigest()
    print(f"verified 256 exact Green-kernel equations; sha256={digest}")


if __name__ == "__main__":
    main()
