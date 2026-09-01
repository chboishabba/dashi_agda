module DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedOperatorDecayRound349Exact where

------------------------------------------------------------------------
-- ROUND349 / BIDI: THE OPERATOR FACE IS A SAME-FAMILY R30 INSTANTIATION
--
-- R348 closes the positive incidence-majorant Schur route.  That does NOT by
-- itself prove the operator products required by Cotlar--Stein.  R30 already
-- owns the exact operator interface, including both T_j^* T_l and T_j T_l^*.
--
-- Under the assumed physical-content premise, the correct next step is simply
-- to name the literal heat-weighted nested shell operator family and place the
-- supplied two-sided product estimates into R30.OperatorCrossShellDecay.
-- No scalar Schur estimate is promoted into an operator-product theorem here.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNCutoffUniformCotlarSteinRound30Exact as R30

record NestedFsOperatorDecayInputs
    {operatorLevel shellLevel : Level}
    {Operator : Set operatorLevel}
    {Shell : Set shellLevel}
    (space : R30.FiniteOperatorSpace Operator)
    (shells : List Shell) : Set (lsuc (operatorLevel ⊔ shellLevel)) where
  field
    -- This is the SAME literal heat-weighted nested shell family on both
    -- Cotlar faces.  A caller may not provide separate left/right operators.
    literalFsOperatorAt : Shell → Operator

    leftEnvelope rightEnvelope : Shell → Shell → ℚ
    leftEnvelopeNonnegative : ∀ left right → 0ℚ ≤ leftEnvelope left right
    rightEnvelopeNonnegative : ∀ left right → 0ℚ ≤ rightEnvelope left right

    adjointThenForwardBound : ∀ left right →
      R30.operatorNorm space
        (R30.composeOperator space
          (R30.adjointOperator space (literalFsOperatorAt left))
          (literalFsOperatorAt right))
      ≤ leftEnvelope left right

    forwardThenAdjointBound : ∀ left right →
      R30.operatorNorm space
        (R30.composeOperator space
          (literalFsOperatorAt left)
          (R30.adjointOperator space (literalFsOperatorAt right)))
      ≤ rightEnvelope left right

open NestedFsOperatorDecayInputs public

nestedFsOperatorCrossShellDecay :
  ∀ {operatorLevel shellLevel}
    {Operator : Set operatorLevel}
    {Shell : Set shellLevel}
    (space : R30.FiniteOperatorSpace Operator)
    (shells : List Shell)
    (I : NestedFsOperatorDecayInputs space shells) →
  R30.OperatorCrossShellDecay space shells (literalFsOperatorAt I)
nestedFsOperatorCrossShellDecay space shells I = record
  { leftEnvelope = leftEnvelope I
  ; rightEnvelope = rightEnvelope I
  ; leftEnvelopeNonnegative = leftEnvelopeNonnegative I
  ; rightEnvelopeNonnegative = rightEnvelopeNonnegative I
  ; adjointThenForwardBound = adjointThenForwardBound I
  ; forwardThenAdjointBound = forwardThenAdjointBound I
  }

round349SameLiteralOperatorFamilyUsedOnBothCotlarFaces : Bool
round349SameLiteralOperatorFamilyUsedOnBothCotlarFaces = true

round349OldR30OperatorDecayInterfaceReused : Bool
round349OldR30OperatorDecayInterfaceReused = true

round349ScalarSchurMajorantPromotedToOperatorDecay : Bool
round349ScalarSchurMajorantPromotedToOperatorDecay = false

round349TwoSidedOperatorDecayPackagingClosed : Bool
round349TwoSidedOperatorDecayPackagingClosed = true

round349CutoffUniformMassClosed : Bool
round349CutoffUniformMassClosed = false

round349CotlarBoundClosed : Bool
round349CotlarBoundClosed = false

round349PackageAClosed : Bool
round349PackageAClosed = false

round349ClayPromotion : Bool
round349ClayPromotion = false

round349TwoSidedOperatorDecayPackagingClosedIsTrue :
  round349TwoSidedOperatorDecayPackagingClosed ≡ true
round349TwoSidedOperatorDecayPackagingClosedIsTrue = refl

round349ScalarSchurMajorantPromotedToOperatorDecayIsFalse :
  round349ScalarSchurMajorantPromotedToOperatorDecay ≡ false
round349ScalarSchurMajorantPromotedToOperatorDecayIsFalse = refl

round349PackageAClosedIsFalse : round349PackageAClosed ≡ false
round349PackageAClosedIsFalse = refl

round349ClayPromotionIsFalse : round349ClayPromotion ≡ false
round349ClayPromotionIsFalse = refl
