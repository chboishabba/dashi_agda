module DASHI.Interop.ITIRLaterMedicalParticularHarmSensibLawAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.ITIRSuiteNormalizedCompilerParityExact as ITIR
import DASHI.Law.SensibLawLaterMedicalParticularHarmSourceConditionedExact as Harm

------------------------------------------------------------------------
-- ITIR NORMALIZED SPINE -> SOURCE-CONDITIONED PARTICULAR HARM
--
-- Medical carriers enter as source artifacts; propositions extracted from
-- them are observed/reviewable before any same-particular-harm or causation
-- promotion.  This preserves the Atomic source-definition / case-outcome split
-- at the ITIR boundary without importing a second identity ontology.
------------------------------------------------------------------------

record ITIRLaterMedicalEvidence : Set₁ where
  constructor itirLaterMedicalEvidence
  field
    medicalEvidence : Harm.LaterMedicalEvidence
    sourceArtifact : ITIR.NormalizedArtifact
    observedArtifact : ITIR.NormalizedArtifact
    reviewableArtifact : ITIR.NormalizedArtifact
    sourceIsArtifact : ITIR.concept sourceArtifact ≡ ITIR.sourceArtifact
    observedIsSignal : ITIR.concept observedArtifact ≡ ITIR.observedSignal
    reviewableIsClaim : ITIR.concept reviewableArtifact ≡ ITIR.reviewableClaim
    extractionReceipt : Set
    adapterReference : String

open ITIRLaterMedicalEvidence public

record ITIRParticularHarmPromotion
    (evidence : ITIRLaterMedicalEvidence) : Set₁ where
  constructor itirParticularHarmPromotion
  field
    harmWeld : Harm.ParticularHarmIdentityWeld
    promotedArtifact : ITIR.NormalizedArtifact
    promotedIsRecord : ITIR.concept promotedArtifact ≡ ITIR.promotedRecord
    promotionReceipt :
      ITIR.PromotionReceipt
        (ITIRLaterMedicalEvidence.reviewableArtifact evidence)
        promotedArtifact
    sameHarmPromotionReference : String

open ITIRParticularHarmPromotion public

record ITIRLaterMedicalParticularHarmParityBoundary : Set where
  constructor itirLaterMedicalParticularHarmParityBoundary
  field
    medicalCarrierStartsAsSourceArtifact : Bool
    medicalCarrierStartsAsSourceArtifactIsTrue :
      medicalCarrierStartsAsSourceArtifact ≡ true
    extractedMedicalPropositionStartsAsObservedSignal : Bool
    extractedMedicalPropositionStartsAsObservedSignalIsTrue :
      extractedMedicalPropositionStartsAsObservedSignal ≡ true
    sameParticularHarmStartsReviewable : Bool
    sameParticularHarmStartsReviewableIsTrue :
      sameParticularHarmStartsReviewable ≡ true
    sameParticularHarmMayBypassPromotion : Bool
    sameParticularHarmMayBypassPromotionIsFalse :
      sameParticularHarmMayBypassPromotion ≡ false
    promotedParticularHarmAutomaticallyPaysCausation : Bool
    promotedParticularHarmAutomaticallyPaysCausationIsFalse :
      promotedParticularHarmAutomaticallyPaysCausation ≡ false

canonicalITIRLaterMedicalParticularHarmParityBoundary :
  ITIRLaterMedicalParticularHarmParityBoundary
canonicalITIRLaterMedicalParticularHarmParityBoundary =
  itirLaterMedicalParticularHarmParityBoundary
    true refl
    true refl
    true refl
    false refl
    false refl

data ParticularHarmBypassesPromotion : Set where
data PromotedParticularHarmAutomaticallyPaysCausation : Set where

particularHarmDoesNotBypassPromotion : ParticularHarmBypassesPromotion → ⊥
particularHarmDoesNotBypassPromotion ()

promotedParticularHarmDoesNotAutoPayCausation :
  PromotedParticularHarmAutomaticallyPaysCausation → ⊥
promotedParticularHarmDoesNotAutoPayCausation ()
