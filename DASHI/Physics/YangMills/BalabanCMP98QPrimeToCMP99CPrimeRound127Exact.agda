{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98QPrimeToCMP99CPrimeRound127Exact where

------------------------------------------------------------------------
-- ROUND127 A1 BIDI MEETING POINT: Q' -> C'
--
-- Round125 gives QC' = -Q'C from the differentiated constraint.  Round124
-- solves one eliminated CMP99 coordinate once the selected row is known to have
-- a nonzero pivot.  This file composes those two facts: after identifying the
-- QC' row contribution with a_c C'_c, the eliminated-coordinate derivative is
-- forced by the literal Q' response.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; NonZero)
open import Relation.Binary.PropositionalEquality using (sym; trans)

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

    -- CMP99 source geometry: C' is supported on the selected eliminated bond,
    -- so the row evaluation QC' is exactly its pivot coefficient times C'_c.
    qAfterCPrimeIsPivotTimesCoordinatePrime :
      Constraint.qAfterCPrime constraintDerivative free row
      ≡ pivotCoefficient * eliminatedCoordinatePrime

open PivotedConstraintDerivative public

asEliminatedPivotData :
  ∀ {Free ConstraintRow} →
  PivotedConstraintDerivative Free ConstraintRow →
  Pivot.EliminatedPivotDerivativeData
asEliminatedPivotData dataSet = record
  { Pivot.EliminatedPivotDerivativeData.pivotCoefficient =
      pivotCoefficient dataSet
  ; Pivot.EliminatedPivotDerivativeData.pivotNonzero = pivotNonzero dataSet
  ; Pivot.EliminatedPivotDerivativeData.qPrimeAfterC =
      Constraint.qPrimeAfterC
        (constraintDerivative dataSet) (free dataSet) (row dataSet)
  ; Pivot.EliminatedPivotDerivativeData.eliminatedCoordinatePrime =
      eliminatedCoordinatePrime dataSet
  ; Pivot.EliminatedPivotDerivativeData.differentiatedPivotEquation =
      trans
        (sym (qAfterCPrimeIsPivotTimesCoordinatePrime dataSet))
        (Constraint.differentiatedConstraint
          (constraintDerivative dataSet) (free dataSet) (row dataSet))
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

-- Physical work has now been reduced to the literal one-step CMP98 Q' formula,
-- the finite-composition source identification from Round126, and the source
-- pivot/nonvanishing statement.  C' itself is no longer an independent lemma.
literalCMP98QPrimePivotInstantiationRound127Level : ProofLevel
literalCMP98QPrimePivotInstantiationRound127Level = conditional
