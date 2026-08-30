{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98QPrimeToCMP99CPrimeRound127Exact where

------------------------------------------------------------------------
-- ROUND127 A1 BIDI MEETING POINT: Q' -> C'
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; NonZero)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109EliminatedCoordinateDerivativeRound125Exact as Constraint
import DASHI.Physics.YangMills.BalabanCMP99EliminatedPivotDerivativeRound124Exact as Pivot

record PivotedConstraintDerivative (Free ConstraintRow : Set) : Set₁ where
  field
    constraintDerivative : Constraint.EliminatedCoordinateDerivativeData Free ConstraintRow
    free : Free
    row : ConstraintRow

    pivotCoefficient : ℚ
    pivotNonzero : NonZero pivotCoefficient
    eliminatedCoordinatePrime : ℚ

    qAfterCPrimeIsPivotTimesCoordinatePrime :
      Constraint.qAfterCPrime constraintDerivative free row
      ≡ pivotCoefficient * eliminatedCoordinatePrime

open PivotedConstraintDerivative public

asEliminatedPivotData :
  ∀ {Free ConstraintRow} →
  PivotedConstraintDerivative Free ConstraintRow →
  Pivot.EliminatedPivotDerivativeData
asEliminatedPivotData dataSet =
  let
    derivative = constraintDerivative dataSet
    freeValue = free dataSet
    rowValue = row dataSet
    qPrime = Constraint.qPrimeAfterC derivative freeValue rowValue
    qCPrime = Constraint.qAfterCPrime derivative freeValue rowValue
    pivot = pivotCoefficient dataSet
    cPrime = eliminatedCoordinatePrime dataSet

    pivotToQCPrime : pivot * cPrime ≡ qCPrime
    pivotToQCPrime = sym (qAfterCPrimeIsPivotTimesCoordinatePrime dataSet)

    pivotPlusQPrimeToQCPrimePlusQPrime :
      pivot * cPrime + qPrime ≡ qCPrime + qPrime
    pivotPlusQPrimeToQCPrimePlusQPrime =
      cong (_+ qPrime) pivotToQCPrime

    swapToSourceOrder : qCPrime + qPrime ≡ qPrime + qCPrime
    swapToSourceOrder = ℚP.+-comm qCPrime qPrime

    sourceZero : qPrime + qCPrime ≡ 0ℚ
    sourceZero = Constraint.differentiatedConstraint derivative freeValue rowValue
  in
  record
    { Pivot.EliminatedPivotDerivativeData.pivotCoefficient = pivot
    ; Pivot.EliminatedPivotDerivativeData.pivotNonzero = pivotNonzero dataSet
    ; Pivot.EliminatedPivotDerivativeData.qPrimeAfterC = qPrime
    ; Pivot.EliminatedPivotDerivativeData.eliminatedCoordinatePrime = cPrime
    ; Pivot.EliminatedPivotDerivativeData.differentiatedPivotEquation =
        trans pivotPlusQPrimeToQCPrimePlusQPrime
          (trans swapToSourceOrder sourceZero)
    }

literalEliminatedCoordinatePrimeExact :
  ∀ {Free ConstraintRow}
    (dataSet : PivotedConstraintDerivative Free ConstraintRow) →
  eliminatedCoordinatePrime dataSet
  ≡ - (Pivot.pivotInverse (asEliminatedPivotData dataSet)
      * Constraint.qPrimeAfterC
          (constraintDerivative dataSet) (free dataSet) (row dataSet))
literalEliminatedCoordinatePrimeExact dataSet =
  Pivot.eliminatedPivotDerivativeExact (asEliminatedPivotData dataSet)

cmp98QPrimeToCMP99CPrimeRound127Level : ProofLevel
cmp98QPrimeToCMP99CPrimeRound127Level = machineChecked

literalCMP98QPrimePivotInstantiationRound127Level : ProofLevel
literalCMP98QPrimePivotInstantiationRound127Level = conditional
