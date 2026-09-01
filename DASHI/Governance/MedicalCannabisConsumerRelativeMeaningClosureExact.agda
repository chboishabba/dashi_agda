module DASHI.Governance.MedicalCannabisConsumerRelativeMeaningClosureExact where

open import DASHI.Core.Prelude

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Reasoning.SemanticConsumerRelativeClosureExact as SemanticClosure
import DASHI.Governance.MedicalCannabisContaminantSemanticEpistemicExact as Cannabis

------------------------------------------------------------------------
-- CONSUMER-RELATIVE MEANING CLOSURE
--
-- A validated contamination observation can be sufficient for a local
-- product-safety consumer while remaining radically insufficient to choose a
-- governance or political-economy explanation.  This is the system-meaning
-- analogue of semantic consumer-relative closure.
------------------------------------------------------------------------

AllMeanings : Cannabis.CannabisMeaning → Set
AllMeanings _ = ⊤

data SafetyConsumerDecision : Set where
  productSafetyReviewRequired : SafetyConsumerDecision

safetyConsumer : Cannabis.CannabisMeaning → SafetyConsumerDecision
safetyConsumer _ = productSafetyReviewRequired

localSafetyConsumerClosedAcrossMeaningFibre :
  Bidi.PointIdentifies AllMeanings safetyConsumer
localSafetyConsumerClosedAcrossMeaningFibre left right leftLive rightLive = refl

------------------------------------------------------------------------
-- Political-economy attribution is a different consumer and is not closed on
-- the same live interpretation fibre.
------------------------------------------------------------------------

data PoliticalEconomyDecision : Set where
  structuralAttributionNotEstablished
  structuralCapitalistHypothesisLive
  : PoliticalEconomyDecision

politicalEconomyConsumer :
  Cannabis.CannabisMeaning → PoliticalEconomyDecision
politicalEconomyConsumer Cannabis.possibleStructuralCapitalistContribution =
  structuralCapitalistHypothesisLive
politicalEconomyConsumer _ = structuralAttributionNotEstablished

politicalEconomyConsumerNotClosedAcrossMeaningFibre :
  Bidi.PointIdentifies AllMeanings politicalEconomyConsumer → ⊥
politicalEconomyConsumerNotClosedAcrossMeaningFibre closed =
  attributionDecisionsDiffer
    (closed
      Cannabis.localProductSafetyMeaning
      Cannabis.possibleStructuralCapitalistContribution
      tt tt)
  where
    attributionDecisionsDiffer :
      structuralAttributionNotEstablished
      ≡ structuralCapitalistHypothesisLive → ⊥
    attributionDecisionsDiffer ()

------------------------------------------------------------------------
-- Reuse the canonical semantic-consumer boundary rather than inventing a new
-- closure doctrine.
------------------------------------------------------------------------

semanticConsumerBoundary : SemanticClosure.SemanticConsumerClosureBoundary
semanticConsumerBoundary = SemanticClosure.canonicalSemanticConsumerClosureBoundary

record MedicalCannabisConsumerMeaningBoundary : Set where
  constructor medicalCannabisConsumerMeaningBoundary
  field
    localSafetyConsumerCanCloseBeforeSystemCause : Bool
    localSafetyConsumerCanCloseBeforeSystemCauseIsTrue :
      localSafetyConsumerCanCloseBeforeSystemCause ≡ true
    politicalEconomyConsumerAutomaticallyClosesFromSameObservation : Bool
    politicalEconomyConsumerAutomaticallyClosesFromSameObservationIsFalse :
      politicalEconomyConsumerAutomaticallyClosesFromSameObservation ≡ false
    actionRelevantClosureEqualsWorldIdentity : Bool
    actionRelevantClosureEqualsWorldIdentityIsFalse :
      actionRelevantClosureEqualsWorldIdentity ≡ false
    safetyActionImpliesStructuralCapitalistAttribution : Bool
    safetyActionImpliesStructuralCapitalistAttributionIsFalse :
      safetyActionImpliesStructuralCapitalistAttribution ≡ false

canonicalMedicalCannabisConsumerMeaningBoundary :
  MedicalCannabisConsumerMeaningBoundary
canonicalMedicalCannabisConsumerMeaningBoundary =
  medicalCannabisConsumerMeaningBoundary
    true refl
    false refl
    false refl
    false refl
