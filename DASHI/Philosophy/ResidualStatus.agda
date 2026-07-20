module DASHI.Philosophy.ResidualStatus where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Residuals are classified before any minimisation policy is selected.

data ResidualKind : Set where
  informationReducible : ResidualKind
  translationRelative : ResidualKind
  constitutive : ResidualKind
  ethicallyPreserved : ResidualKind
  damageEvidence : ResidualKind
  genuineDifference : ResidualKind
  unresolvedObstruction : ResidualKind

record ResidualAssessment (Residual Evidence Action : Set) : Set₁ where
  field
    residual : Residual
    kind : ResidualKind
    evidence : Evidence
    proposedAction : Action
    minimisationRequired : Bool
    preservationRequired : Bool
    reassessmentRequired : Bool

open ResidualAssessment public

record ResidualBoundary : Set where
  constructor mkResidualBoundary
  field
    everyResidualIsError : Bool
    everyResidualShouldVanish : Bool
    someResidualsShouldBePreserved : Bool
    classificationBeforeAction : Bool

open ResidualBoundary public

canonicalResidualBoundary : ResidualBoundary
canonicalResidualBoundary =
  mkResidualBoundary false false true true

canonicalResidualNeedNotVanish :
  everyResidualShouldVanish canonicalResidualBoundary ≡ false
canonicalResidualNeedNotVanish = refl
