{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP99EliminatedPivotDerivativeRound124Exact where

------------------------------------------------------------------------
-- ROUND124 A1 FORWARD SOURCE ALGEBRA: DIFFERENTIATE THE CMP99 ELIMINATED PIVOT
--
-- Primary source:
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Commun. Math. Phys. 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- After the CMP99 coordinate elimination, the selected coordinate in one
-- constraint row is fixed by
--
--       (Q(U) C(U) B)(c) = 0.
--
-- Differentiating gives
--
--       a_c C'_c(B) + (Q' C B)(c) = 0.
--
-- For non-zero pivot coefficient a_c this file proves constructively
--
--       C'_c(B) = - a_c^{-1} (Q' C B)(c).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; 1/_; NonZero)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record EliminatedPivotDerivativeData : Set where
  field
    pivotCoefficient : ℚ
    pivotNonzero : NonZero pivotCoefficient
    qPrimeAfterC : ℚ
    eliminatedCoordinatePrime : ℚ

    differentiatedPivotEquation :
      pivotCoefficient * eliminatedCoordinatePrime + qPrimeAfterC ≡ 0ℚ

open EliminatedPivotDerivativeData public

pivotInverse : EliminatedPivotDerivativeData → ℚ
pivotInverse dataSet =
  let instance nonzero = pivotNonzero dataSet
  in 1/ pivotCoefficient dataSet

pivotInverseRight : ∀ dataSet →
  pivotCoefficient dataSet * pivotInverse dataSet ≡ 1ℚ
pivotInverseRight dataSet =
  let instance nonzero = pivotNonzero dataSet
  in ℚP.*-inverseʳ (pivotCoefficient dataSet)

eliminatedPivotDerivativeExact : ∀ dataSet →
  eliminatedCoordinatePrime dataSet
  ≡ - (pivotInverse dataSet * qPrimeAfterC dataSet)
eliminatedPivotDerivativeExact dataSet =
  let
    a = pivotCoefficient dataSet
    aInv = pivotInverse dataSet
    cPrime = eliminatedCoordinatePrime dataSet
    source = qPrimeAfterC dataSet

    scaled : aInv * (a * cPrime + source) ≡ aInv * 0ℚ
    scaled = cong (aInv *_) (differentiatedPivotEquation dataSet)

    simplify : aInv * (a * cPrime + source) ≡ cPrime + aInv * source
    simplify =
      trans
        (ℚRing.solve-∀ aInv a cPrime source)
        (cong (λ selected → selected * cPrime + aInv * source)
          (trans (ℚP.*-comm aInv a) (pivotInverseRight dataSet)))

    zeroRight : aInv * 0ℚ ≡ 0ℚ
    zeroRight = ℚP.*-zeroʳ aInv

    sumZero : cPrime + aInv * source ≡ 0ℚ
    sumZero = trans (sym simplify) (trans scaled zeroRight)
  in
  trans
    (ℚRing.solve-∀ cPrime aInv source)
    (trans
      (cong (λ selected → selected - aInv * source) sumZero)
      (ℚRing.solve-∀ aInv source))

cmp99EliminatedPivotDerivativeAlgebraRound124Level : ProofLevel
cmp99EliminatedPivotDerivativeAlgebraRound124Level = machineChecked

literalCMP99PivotAndQPrimeInstantiationRound124Level : ProofLevel
literalCMP99PivotAndQPrimeInstantiationRound124Level = conditional
