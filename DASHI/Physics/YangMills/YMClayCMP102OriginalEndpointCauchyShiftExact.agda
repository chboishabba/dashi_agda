module DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact where

------------------------------------------------------------------------
-- CMP102 original all-degree native Bishop Cauchy endpoint cut.
-- SOURCE WRITTEN, AGDA KERNEL NOT RUN. No new factorial/order/real carrier.
-- Preserve original signs, degree-zero singleton, and last even endpoint.
--
-- Original owners: Cauchy/Newton, Bishop/Bridges, Murray/Csimma;
-- DASHI Row / original exponential-parity / CMP109 source formulas.
--
-- This master-compatible source uses *definitionally identical* CMP109
-- coefficients, not an import of diverged research PR #1444.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 1ℚᵘ; 0ℚᵘ)
open import Data.Fin.Base using (toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Base as N
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality using (cong)

import Algebra.Properties.Semiring.Sum as SemiringSum
import Real as R
import RealProperties as P

import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopUnsignedFactorialCauchyParitySplitExact as Unsigned
import DASHI.Foundations.BishopSignTwistedFiniteCauchyCoefficientExact as Twist
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as E
import DASHI.Physics.YangMills.YMClayCMP102NativeMasterSignedParitySpecializationExact as Original
import DASHI.Physics.YangMills.YMClayCMP102MasterPositiveABCoefficientSourceWeldExact as Weld

module BishopSum = SemiringSum P.+-*-semiring

-- This is the precise original positive A/B coefficient formula in #1444.
-- Merely an alias, not a second factorial source or a second represented limit.
aCoefficient bCoefficient : Nat → R.ℝ
aCoefficient n = R._⋆ (E.inverseFactorialRational (E.evenExponent (suc n)))
bCoefficient n = R._⋆ (E.inverseFactorialRational (E.oddExponent (suc n)))

two : R.ℝ
two = R._⋆ (+ 2 / 1)

evenPart oddPart : Nat → R.ℝ
evenPart zero = R._*_ two (aCoefficient zero)
evenPart (suc n) =
  R._+_
    (R._*_ two (aCoefficient (suc n)))
    (Row.cauchyCoefficient aCoefficient aCoefficient n)

oddPart zero = R.1ℝ
oddPart (suc zero) = R._*_ two (bCoefficient zero)
oddPart (suc (suc n)) =
  R._+_
    (R._*_ two (bCoefficient (suc n)))
    (Row.cauchyCoefficient bCoefficient bCoefficient n)

-- One existing original stdlib Fin-sum operation pays the final endpoint.
-- The truncated Nat subtraction is used only on the Fin-bounded source.
cauchySplitLast :
  (left right : Nat → R.ℝ) → ∀ n →
  R._≃_
    (Row.cauchyCoefficient left right (suc n))
    (R._+_
      (Row.cauchyCoefficient left (Row.shift right) n)
      (R._*_ (left (suc n)) (right zero)))
cauchySplitLast left right n =
  P.≃-trans
    (BishopSum.sum-init-last
      (λ index →
        R._*_ (left (toℕ index))
          (right (suc n N.∸ toℕ index))))
    (P.+-cong
      (BishopSum.sum-cong-≋
        (λ index →
          P.*-congˡ
            (P.≃-refl₂
              (cong right
                (NP.∸-suc (FinP.toℕ≤pred[n] index))))))
      P.≃-refl)

-- First and last original Cauchy terms, with the native shifted interior.
cauchyTwoEndpoints :
  (f : Nat → R.ℝ) → ∀ n →
  R._≃_
    (Row.cauchyCoefficient f f (suc (suc n)))
    (R._+_
      (R._*_ (f zero) (f (suc (suc n))))
      (R._+_
        (Row.cauchyCoefficient (Row.shift f) (Row.shift f) n)
        (R._*_ (f (suc (suc n))) (f zero))))
cauchyTwoEndpoints f n =
  P.≃-trans
    (Row.cauchyCoefficientSuccessor f f (suc n))
    (P.+-cong P.≃-refl
      (cauchySplitLast (Row.shift f) f n))

-- In the original exponential source the zero-th even and odd factorial
-- terms are both exactly 1, including the odd 1/1! coefficient.
evenUnitZero : R._≃_ (Unsigned.evenExp R.1ℝ zero) R.1ℝ
evenUnitZero =
  let open P.ℝ-Solver
  in solve 0
    ((Κ 1ℚᵘ ⊗ Κ (+ 1 / 1)) ⊜ Κ 1ℚᵘ)
    P.≃-refl

oddUnitZero : R._≃_ (Unsigned.oddExp R.1ℝ zero) R.1ℝ
oddUnitZero =
  let open P.ℝ-Solver
  in solve 0
    (((Κ 1ℚᵘ ⊗ Κ 1ℚᵘ) ⊗ Κ (+ 1 / 1)) ⊜ Κ 1ℚᵘ)
    P.≃-refl

cauchyDegreeOneUnit :
  (f : Nat → R.ℝ) →
  R._≃_ (f zero) R.1ℝ →
  R._≃_
    (Row.cauchyCoefficient f f (suc zero))
    (R._*_ two (f (suc zero)))
cauchyDegreeOneUnit f unit =
  P.≃-trans
    (Row.cauchyCoefficientSuccessor f f zero)
    (P.≃-trans
      (P.+-cong P.≃-refl
        (Row.cauchyCoefficientZero (Row.shift f) f))
      (P.≃-trans
        (P.+-cong
          (P.*-congʳ unit)
          (P.*-congˡ unit))
        (let open P.ℝ-Solver
         in solve 1
            (λ x →
              (Κ 1ℚᵘ ⊗ x) ⊕ (x ⊗ Κ 1ℚᵘ)
              ⊜ Κ (+ 2 / 1) ⊗ x)
            P.≃-refl (f (suc zero)))))

cauchyDegreeTwoPlusUnit :
  (f : Nat → R.ℝ) →
  R._≃_ (f zero) R.1ℝ →
  ∀ n →
  R._≃_
    (Row.cauchyCoefficient f f (suc (suc n)))
    (R._+_
      (R._*_ two (f (suc (suc n))))
      (Row.cauchyCoefficient (Row.shift f) (Row.shift f) n))
cauchyDegreeTwoPlusUnit f unit n =
  P.≃-trans
    (cauchyTwoEndpoints f n)
    (P.≃-trans
      (P.+-cong
        (P.*-congʳ unit)
        (P.+-cong P.≃-refl (P.*-congˡ unit)))
      (let
         x = f (suc (suc n))
         c = Row.cauchyCoefficient (Row.shift f) (Row.shift f) n
         open P.ℝ-Solver
       in solve 2
          (λ x′ c′ →
            (Κ 1ℚᵘ ⊗ x′) ⊕ (c′ ⊕ (x′ ⊗ Κ 1ℚᵘ))
            ⊜ (Κ (+ 2 / 1) ⊗ x′) ⊕ c′)
          P.≃-refl x c))

-- Reuse the exact source CMP109 factorial identities from the prior
-- master-native weld, then reuse the existing original finite Cauchy sum
-- congruence on the original Nat/Fin support.
evenInteriorOriginal : ∀ n →
  R._≃_
    (Row.cauchyCoefficient
      (Row.shift (Unsigned.evenExp R.1ℝ))
      (Row.shift (Unsigned.evenExp R.1ℝ)) n)
    (Row.cauchyCoefficient aCoefficient aCoefficient n)
evenInteriorOriginal n =
  Twist.rowCauchyCoefficientRespectsTerms
    (Row.shift (Unsigned.evenExp R.1ℝ))
    (Row.shift (Unsigned.evenExp R.1ℝ))
    aCoefficient aCoefficient
    Weld.masterEvenShiftIsOriginalCMP109A
    Weld.masterEvenShiftIsOriginalCMP109A n

oddInteriorOriginal : ∀ n →
  R._≃_
    (Row.cauchyCoefficient
      (Row.shift (Unsigned.oddExp R.1ℝ))
      (Row.shift (Unsigned.oddExp R.1ℝ)) n)
    (Row.cauchyCoefficient bCoefficient bCoefficient n)
oddInteriorOriginal n =
  Twist.rowCauchyCoefficientRespectsTerms
    (Row.shift (Unsigned.oddExp R.1ℝ))
    (Row.shift (Unsigned.oddExp R.1ℝ))
    bCoefficient bCoefficient
    Weld.masterOddShiftIsOriginalCMP109B
    Weld.masterOddShiftIsOriginalCMP109B n

-- The original full even row is exactly the original CMP109 A polynomial
-- coefficient, for ALL natural degrees, including n=0 and both endpoints.
originalEvenRowIsNativeAPart : ∀ n →
  R._≃_
    (Row.cauchyCoefficient
      (Unsigned.evenExp R.1ℝ)
      (Unsigned.evenExp R.1ℝ) (suc n))
    (evenPart n)
originalEvenRowIsNativeAPart zero =
  P.≃-trans
    (cauchyDegreeOneUnit (Unsigned.evenExp R.1ℝ) evenUnitZero)
    (P.*-congˡ (Weld.masterEvenShiftIsOriginalCMP109A zero))
originalEvenRowIsNativeAPart (suc n) =
  P.≃-trans
    (cauchyDegreeTwoPlusUnit (Unsigned.evenExp R.1ℝ) evenUnitZero n)
    (P.+-cong
      (P.*-congˡ (Weld.masterEvenShiftIsOriginalCMP109A (suc n)))
      (evenInteriorOriginal n))

-- Original odd factorial row: singleton n=0, two endpoints at n=1,
-- and two endpoints plus shifted B Cauchy interior for all n>=2.
originalOddRowIsNativeBPart : ∀ n →
  R._≃_
    (Row.cauchyCoefficient
      (Unsigned.oddExp R.1ℝ)
      (Unsigned.oddExp R.1ℝ) n)
    (oddPart n)
originalOddRowIsNativeBPart zero =
  P.≃-trans
    (Row.cauchyCoefficientZero
      (Unsigned.oddExp R.1ℝ) (Unsigned.oddExp R.1ℝ))
    (P.≃-trans
      (P.*-cong oddUnitZero oddUnitZero)
      (let open P.ℝ-Solver
       in solve 0 (Κ 1ℚᵘ ⊗ Κ 1ℚᵘ ⊜ Κ 1ℚᵘ)
          P.≃-refl))
originalOddRowIsNativeBPart (suc zero) =
  P.≃-trans
    (cauchyDegreeOneUnit (Unsigned.oddExp R.1ℝ) oddUnitZero)
    (P.*-congˡ (Weld.masterOddShiftIsOriginalCMP109B zero))
originalOddRowIsNativeBPart (suc (suc n)) =
  P.≃-trans
    (cauchyDegreeTwoPlusUnit (Unsigned.oddExp R.1ℝ) oddUnitZero n)
    (P.+-cong
      (P.*-congˡ (Weld.masterOddShiftIsOriginalCMP109B (suc n)))
      (oddInteriorOriginal n))

-- The original signed odd row has the same Fin support, with precisely
-- one negative factor. Pull that sign outside the Cauchy coefficient;
-- do not infer it from an unsigned binomial identity.
cauchyNegatedRight :
  (left right : Nat → R.ℝ) → ∀ n →
  R._≃_
    (Row.cauchyCoefficient left (λ k → R.- (right k)) n)
    (R.- (Row.cauchyCoefficient left right n))
cauchyNegatedRight left right n =
  P.≃-trans
    (BishopSum.sum-cong-≋
      (λ index →
        let
          x = left (toℕ index)
          y = right (n N.∸ toℕ index)
          open P.ℝ-Solver
        in solve 2
          (λ x′ y′ →
            x′ ⊗ (⊝ y′) ⊜ (⊝ Κ 1ℚᵘ) ⊗ (x′ ⊗ y′))
          P.≃-refl x y))
    (P.≃-trans
      (P.≃-symm
        (BishopSum.*-distribˡ-sum
          (R.- R.1ℝ)
          (λ index →
            R._*_ (left (toℕ index))
                  (right (n N.∸ toℕ index)))))
      (let open P.ℝ-Solver
       in solve 1
         (λ x → (⊝ Κ 1ℚᵘ) ⊗ x ⊜ ⊝ x)
         P.≃-refl (Row.cauchyCoefficient left right n)))

-- These are the TWO specific original A/B signed row witnesses that the
-- earlier #1444 conditional shifted-coefficient consumer required.
-- Their target expressions are definitionally identical to the #1444
-- formulas; exact same-module Agda imports are still a branch integration
-- obligation, and must not be claimed here.
originalSignedEvenRowIsNativeAPart : ∀ n →
  R._≃_ (Original.originalEvenExponentialRow n) (evenPart n)
originalSignedEvenRowIsNativeAPart n =
  P.≃-trans
    (Weld.originalEvenRowAsPositive n)
    (originalEvenRowIsNativeAPart n)

originalSignedOddRowIsNegativeNativeBPart : ∀ n →
  R._≃_ (Original.originalOddExponentialRow n) (R.- (oddPart n))
originalSignedOddRowIsNegativeNativeBPart n =
  P.≃-trans
    (Weld.originalOddRowAsSignedPositive n)
    (P.≃-trans
      (cauchyNegatedRight
        (Unsigned.oddExp R.1ℝ)
        (Unsigned.oddExp R.1ℝ) n)
      (P.-‿cong (originalOddRowIsNativeBPart n)))

-- All-degree shifted original CMP109 algebraic bracket is zero.
-- No formal-series Cauchy limit, analytic chart, or physical SU(N) T.
shiftedNativeBracketCoefficient : Nat → R.ℝ
shiftedNativeBracketCoefficient n = R._-_ (oddPart n) (evenPart n)

shiftedNativeBracketCoefficientZero : ∀ n →
  R._≃_ (shiftedNativeBracketCoefficient n) R.0ℝ
shiftedNativeBracketCoefficientZero n =
  let
    e = evenPart n
    o = oddPart n
    open P.ℝ-Solver
  in
  P.≃-trans
    (solve 2
      (λ x y → y ⊖ x ⊜ ⊝ (x ⊕ (⊝ y)))
      P.≃-refl e o)
    (P.≃-trans
      (P.-‿cong
        (P.≃-trans
          (P.+-cong
            (P.≃-symm (originalSignedEvenRowIsNativeAPart n))
            (P.≃-symm (originalSignedOddRowIsNegativeNativeBPart n)))
          (Original.originalSignedEvenOddRowZero n)))
      P.0≃-0)
