module DASHI.Physics.CalciumTelepathyObservationMechanismCutExact where

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.InverseProblemIdentifiabilityBidiExact as Inverse
import DASHI.Reasoning.FibreRoutingSufficiencyCausalInterventionSnowballExact as Causal

-- Authors of the biological hypothesis, not DASHI, own the physiological
-- assertion. This file proves only finite epistemic/model-selection facts.

data BiologicalInterpretation : Set where
  ordinaryChannelModulation
    proposedAdditionalInformationChannel : BiologicalInterpretation

data SubjectiveReadout : Set where
  unusualHearingExperience : SubjectiveReadout

subjective : BiologicalInterpretation → SubjectiveReadout
subjective _ = unusualHearingExperience

biologicalIdentity : BiologicalInterpretation → BiologicalInterpretation
biologicalIdentity x = x

subjectiveCollision :
  INF.NonFactorabilityWitness subjective biologicalIdentity
subjectiveCollision = INF.nonFactorabilityWitness
  ordinaryChannelModulation proposedAdditionalInformationChannel refl (λ ())

subjectiveReadoutCannotIdentifyCoupling :
  INF.FactorsThrough subjective biologicalIdentity → ⊥
subjectiveReadoutCannotIdentifyCoupling =
  INF.witnessRulesOutEveryFlatFactorisation subjectiveCollision

data IndependentlyDecodableMessage : Set where
  noAboveChanceDecoding
  aboveChanceDecoding : IndependentlyDecodableMessage

-- Illustrative *hypothesis-prediction* function. Does not assert that such
-- a result has occurred or that a true biological model is identifiable.
predictedDecoding :
  BiologicalInterpretation → IndependentlyDecodableMessage
predictedDecoding ordinaryChannelModulation = noAboveChanceDecoding
predictedDecoding proposedAdditionalInformationChannel = aboveChanceDecoding

jointReadout : Inverse.MultiChannelModel
jointReadout = Inverse.multi-channel-model
  BiologicalInterpretation SubjectiveReadout IndependentlyDecodableMessage
  subjective predictedDecoding
  "hypothetical channel-signature model; requires independent controlled data"

jointSeparates : Inverse.FusionSeparates jointReadout
jointSeparates = Inverse.fusion-separates go
  where
  go : (x y : BiologicalInterpretation) →
    Inverse.f₁ jointReadout x ≡ Inverse.f₁ jointReadout y →
    Inverse.f₂ jointReadout x ≡ Inverse.f₂ jointReadout y →
    x ≡ y
  go ordinaryChannelModulation ordinaryChannelModulation _ _ = refl
  go ordinaryChannelModulation proposedAdditionalInformationChannel _ ()
  go proposedAdditionalInformationChannel ordinaryChannelModulation _ ()
  go proposedAdditionalInformationChannel proposedAdditionalInformationChannel _ _ = refl

causalOwner : Causal.FibreSufficiencyCausalInterventionBoundary
causalOwner = Causal.canonicalFibreSufficiencyCausalInterventionBoundary
