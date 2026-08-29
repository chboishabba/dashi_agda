{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP99EliminatedPivotDerivativeRound108Exact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; 1/_; NonZero)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

-- CMP99, after (3.156): on an eliminated pivot coordinate the differentiated
-- fixed constraint is a one-dimensional linear solve
--
--   a_c C'_c + (Q' C)_c = 0.
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

cmp99EliminatedPivotDerivativeRound108Level : ProofLevel
cmp99EliminatedPivotDerivativeRound108Level = machineChecked

-- Physical leaves: identify the literal CMP99 pivot coefficient, prove its
-- nonvanishing on the admitted small-field domain, and instantiate Q' C from
-- the differentiated CMP98/CMP99 averaging operator.
cmp99LiteralEliminatedPivotCoefficientRound108Level : ProofLevel
cmp99LiteralEliminatedPivotCoefficientRound108Level = conditional

cmp99LiteralQPrimeAfterCRound108Level : ProofLevel
cmp99LiteralQPrimeAfterCRound108Level = conditional
