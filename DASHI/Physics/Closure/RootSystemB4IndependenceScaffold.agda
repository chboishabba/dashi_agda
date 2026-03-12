module DASHI.Physics.Closure.RootSystemB4IndependenceScaffold where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.Validation.RootSystemB4ShellComparison as B4C

data MissingOrientationSignaturePromotion : Set where
  missingOrientationSignaturePromotion : MissingOrientationSignaturePromotion

data MissingAdmissibleDynamicsWitness : Set where
  missingAdmissibleDynamicsWitness : MissingAdmissibleDynamicsWitness

data MissingObservableSignatureAgreement : Set where
  missingObservableSignatureAgreement : MissingObservableSignatureAgreement

data MissingRealizationIndependencePayload : Set where
  missingRealizationIndependencePayload : MissingRealizationIndependencePayload

record RootSystemB4IndependentCoreWitnessObligations : Setω where
  field
    shellComparisonAvailable : B4C.B4ShellComparisonReport
    promotionStillBlocked :
      B4C.B4ShellComparisonReport.promotionStatus shellComparisonAvailable
      ≡ B4C.standaloneOnly
    needsOrientationSignaturePromotion :
      MissingOrientationSignaturePromotion
    needsAdmissibleDynamicsWitness :
      MissingAdmissibleDynamicsWitness
    needsObservableSignatureAgreement :
      MissingObservableSignatureAgreement
    needsRealizationIndependencePayload :
      MissingRealizationIndependencePayload

b4IndependentCoreWitnessObligations :
  RootSystemB4IndependentCoreWitnessObligations
b4IndependentCoreWitnessObligations =
  record
    { shellComparisonAvailable = B4C.report
    ; promotionStillBlocked = refl
    ; needsOrientationSignaturePromotion =
        missingOrientationSignaturePromotion
    ; needsAdmissibleDynamicsWitness =
        missingAdmissibleDynamicsWitness
    ; needsObservableSignatureAgreement =
        missingObservableSignatureAgreement
    ; needsRealizationIndependencePayload =
        missingRealizationIndependencePayload
    }
