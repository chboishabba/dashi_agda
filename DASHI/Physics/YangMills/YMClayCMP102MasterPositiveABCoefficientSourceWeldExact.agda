module DASHI.Physics.YangMills.YMClayCMP102MasterPositiveABCoefficientSourceWeldExact where

------------------------------------------------------------------------
-- Master-native CMP102 coefficient/source weld on original Bishop ℝ.
-- Reuse the original signed exponential Cauchy row, native even/odd
-- exponent encoding, the original Fin-sum Cauchy term congruence and
-- the source CMP109 shifted inverse-factorial expressions from #1444.
--
-- NO new factorial engine / analytic series / physical field carrier.
-- This does not claim the #1444 finite-two-endpoint/CMP109 G coefficient
-- is already identified; that final original-row attachment is OPEN.
-- All theorem bodies SOURCE WRITTEN, not Agda-2.9 kernel verified.
-- Original authors: Cauchy/binomial, Bishop/Bridges, Murray/Csimma,
-- existing DASHI parity, Exp, sign and CMP109 owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (sym)
import Real as R
import RealProperties as RP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopUnsignedFactorialCauchyParitySplitExact as Unsigned
import DASHI.Foundations.BishopSignTwistedFiniteCauchyCoefficientExact as Twist
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopRound11SignedFactorialExponentEncodingExact as Encoding
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Signs
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as E
import DASHI.Physics.YangMills.YMClayCMP102NativeMasterSignedParitySpecializationExact as Original

-- The same inverseFactorialRational owner used by original #1444 CMP109.
-- These are equivalence witnesses, NOT duplicate A/B series definitions.

unitPower : ∀ n → R._≃_ (R.pow R.1ℝ n) R.1ℝ
unitPower zero = RP.≃-refl
unitPower (suc n) =
  RP.≃-trans
    (RP.*-congʳ (unitPower n))
    (RP.*-identityˡ R.1ℝ)

unitExponentialTermIsOriginalInverseFactorial : ∀ n →
  R._≃_ (Exp.expTerm R.1ℝ n)
          (R._⋆ (E.inverseFactorialRational n))
unitExponentialTermIsOriginalInverseFactorial n =
  RP.≃-trans
    (RP.*-congʳ (unitPower n))
    (RP.*-identityˡ (R._⋆ (E.inverseFactorialRational n)))

masterEvenShiftIsOriginalCMP109A : ∀ k →
  R._≃_
    (Unsigned.evenExp R.1ℝ (suc k))
    (R._⋆ (E.inverseFactorialRational (E.evenExponent (suc k))))
masterEvenShiftIsOriginalCMP109A k
  rewrite sym (Encoding.evenExponentIsDoubledIndex (suc k)) =
  unitExponentialTermIsOriginalInverseFactorial
    (E.evenExponent (suc k))

masterOddShiftIsOriginalCMP109B : ∀ k →
  R._≃_
    (Unsigned.oddExp R.1ℝ (suc k))
    (R._⋆ (E.inverseFactorialRational (E.oddExponent (suc k))))
masterOddShiftIsOriginalCMP109B k
  rewrite sym (Encoding.oddExponentIsSuccessorDoubled (suc k)) =
  unitExponentialTermIsOriginalInverseFactorial
    (E.oddExponent (suc k))

-- Preserve the original signs BEFORE moving to shifted A/B coordinates.

negativeUnitEvenTermIsPositive : ∀ k →
  R._≃_ (Unsigned.evenExp (R.- R.1ℝ) k)
          (Unsigned.evenExp R.1ℝ k)
negativeUnitEvenTermIsPositive k
  rewrite sym (Encoding.evenExponentIsDoubledIndex k) =
  RP.*-congʳ (Signs.evenPowerNegation R.1ℝ k)

negativeUnitOddTermIsNegative : ∀ k →
  R._≃_ (Unsigned.oddExp (R.- R.1ℝ) k)
          (R.- (Unsigned.oddExp R.1ℝ k))
negativeUnitOddTermIsNegative k
  rewrite sym (Encoding.oddExponentIsSuccessorDoubled k) =
  let
    power = R.pow R.1ℝ (E.oddExponent k)
    coefficient = R._⋆ (E.inverseFactorialRational (E.oddExponent k))
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.*-congʳ (Signs.oddPowerNegation R.1ℝ k))
    (solve 2
      (λ x y → (⊝ x) ⊗ y ⊜ ⊝ (x ⊗ y))
      RP.≃-refl power coefficient)

-- Fin(suc degree) congruence on the ORIGINAL master Cauchy row;
-- neither a new reindex theorem nor a new summation carrier.

originalEvenRowAsPositive : ∀ n →
  R._≃_
    (Original.originalEvenExponentialRow n)
    (Row.cauchyCoefficient
      (Unsigned.evenExp R.1ℝ)
      (Unsigned.evenExp R.1ℝ) (suc n))
originalEvenRowAsPositive n =
  Twist.rowCauchyCoefficientRespectsTerms
    (Unsigned.evenExp R.1ℝ)
    (Unsigned.evenExp (R.- R.1ℝ))
    (Unsigned.evenExp R.1ℝ)
    (Unsigned.evenExp R.1ℝ)
    (λ k → RP.≃-refl)
    negativeUnitEvenTermIsPositive (suc n)

originalOddRowAsSignedPositive : ∀ n →
  R._≃_
    (Original.originalOddExponentialRow n)
    (Row.cauchyCoefficient
      (Unsigned.oddExp R.1ℝ)
      (λ k → R.- (Unsigned.oddExp R.1ℝ k)) n)
originalOddRowAsSignedPositive n =
  Twist.rowCauchyCoefficientRespectsTerms
    (Unsigned.oddExp R.1ℝ)
    (Unsigned.oddExp (R.- R.1ℝ))
    (Unsigned.oddExp R.1ℝ)
    (λ k → R.- (Unsigned.oddExp R.1ℝ k))
    (λ k → RP.≃-refl)
    negativeUnitOddTermIsNegative n

-- All-degree original Bishop positive-even / signed-odd Cauchy equality.
-- It is already a source-native consequence of original signed zero.
-- To obtain #1444 G(X), still split both endpoints to native A/B.

originalPositiveEvenAndSignedOddRowsCancel : ∀ n →
  R._≃_
    (R._+_
      (Row.cauchyCoefficient
        (Unsigned.evenExp R.1ℝ)
        (Unsigned.evenExp R.1ℝ) (suc n))
      (Row.cauchyCoefficient
        (Unsigned.oddExp R.1ℝ)
        (λ k → R.- (Unsigned.oddExp R.1ℝ k)) n))
    R.0ℝ
originalPositiveEvenAndSignedOddRowsCancel n =
  RP.≃-trans
    (RP.+-cong
      (RP.≃-symm (originalEvenRowAsPositive n))
      (RP.≃-symm (originalOddRowAsSignedPositive n)))
    (Original.originalSignedEvenOddRowZero n)
