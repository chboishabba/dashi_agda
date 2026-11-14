module DASHI.Governance.EpistemicPowerTetralemmaBridgeExact where

-- Formal alignment between the existing disagreement/tetralemma carrier
-- and epistemic support flags. Not an equivalence with historical Buddhist
-- catuskoti, nor with the four-view agent matrix or four residual levels.

open import DASHI.Core.Prelude
import DASHI.Algebra.TetralemmaBridge as Tetralemma
import DASHI.Algebra.DisagreementFourViewBoundary as FourView
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.EpistemicPowerStructuralRetentionExact as Power

statusToPosition : Power.EvidenceStatus → Tetralemma.TetralemmaPosition
statusToPosition Power.affirmed = Tetralemma.affirmation
statusToPosition Power.denied = Tetralemma.negation
statusToPosition Power.conflicting = Tetralemma.both
statusToPosition Power.undetermined = Tetralemma.neither

positionToStatus : Tetralemma.TetralemmaPosition → Power.EvidenceStatus
positionToStatus Tetralemma.affirmation = Power.affirmed
positionToStatus Tetralemma.negation = Power.denied
positionToStatus Tetralemma.both = Power.conflicting
positionToStatus Tetralemma.neither = Power.undetermined

statusPositionRoundTrip :
  (status : Power.EvidenceStatus) →
  positionToStatus (statusToPosition status) ≡ status
statusPositionRoundTrip Power.affirmed = refl
statusPositionRoundTrip Power.denied = refl
statusPositionRoundTrip Power.conflicting = refl
statusPositionRoundTrip Power.undetermined = refl

positionStatusRoundTrip :
  (position : Tetralemma.TetralemmaPosition) →
  statusToPosition (positionToStatus position) ≡ position
positionStatusRoundTrip Tetralemma.affirmation = refl
positionStatusRoundTrip Tetralemma.negation = refl
positionStatusRoundTrip Tetralemma.both = refl
positionStatusRoundTrip Tetralemma.neither = refl

matchesExistingPolarAssessment :
  (positive negative : Bool) →
  statusToPosition (Power.encode positive negative)
  ≡ FourView.polarPosition (FourView.assess positive negative)
matchesExistingPolarAssessment true true = refl
matchesExistingPolarAssessment true false = refl
matchesExistingPolarAssessment false true = refl
matchesExistingPolarAssessment false false = refl

-- Two agent-view configurations share the same first-order report but
-- differ on the second-order model of the institution's interlocutor.
-- A polar-status summary cannot recover that missing relation.
data Voice : Set where
  acceptsClaim disputesClaim : Voice

firstOrder : FourView.FourViewMatrix Voice → Voice
firstOrder = FourView.aOwn

secondOrder : FourView.FourViewMatrix Voice → Voice
secondOrder = FourView.aModelsB

configurationOne : FourView.FourViewMatrix Voice
configurationOne =
  FourView.fourViews
    acceptsClaim acceptsClaim acceptsClaim acceptsClaim

configurationTwo : FourView.FourViewMatrix Voice
configurationTwo =
  FourView.fourViews
    acceptsClaim acceptsClaim disputesClaim acceptsClaim

firstOrderReportCannotRecoverSecondOrderModel :
  INF.NonFactorabilityWitness firstOrder secondOrder
firstOrderReportCannotRecoverSecondOrderModel =
  INF.nonFactorabilityWitness
    configurationOne configurationTwo refl (λ ())

firstOrderRechartCannotRecoverSecondOrderModel :
  ∀ {R : Set} (f : Voice → R) →
  INF.FactorsThrough
    (λ state → f (firstOrder state)) secondOrder → ⊥
firstOrderRechartCannotRecoverSecondOrderModel f =
  INF.rechartingCannotRecoverErasedPhenomenon
    f firstOrderReportCannotRecoverSecondOrderModel
