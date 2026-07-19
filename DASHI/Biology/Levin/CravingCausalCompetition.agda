module DASHI.Biology.Levin.CravingCausalCompetition where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.MicrobiomeHostAppetiteBoundary as Microbiome
import DASHI.Biology.Levin.BoundaryHiddenStateNonrecurrence as Hidden

record CravingHypothesisSet : Set where
  field
    nutrientDeficiencyRoute : Bool
    energyHomeostasisRoute : Bool
    microbialMetaboliteRoute : Bool
    hormonalRoute : Bool
    learnedAssociationRoute : Bool
    sensoryRewardRoute : Bool
    stressAndAffectRoute : Bool
    medicationOrDiseaseRoute : Bool
    culturalAvailabilityRoute : Bool

record CravingDiscriminationProtocol : Set where
  field
    nutrientStatusMeasured : Bool
    microbiomeStateMeasured : Bool
    endocrineStateMeasured : Bool
    temporalOrderMeasured : Bool
    interventionSpecified : Bool
    placeboAndExpectancyControlled : Bool
    repeatedWithinPersonSampling : Bool
    competingModelsCompared : Bool

record CravingCausalCompetitionBoundary : Set where
  field
    appetiteBoundary : Microbiome.MicrobiomeHostAppetiteBoundary
    hiddenStateBoundary : Hidden.NonrecurrenceBoundary
    cravingMayReflectDeficiency : Bool
    cravingReliablyDiagnosesDeficiency : Bool
    cravingMayReflectMicrobialInfluence : Bool
    cravingIsMicrobialCommand : Bool
    oneBehaviourMayHaveMultipleInternalCauses : Bool
    clinicalInferenceBlockedWithoutMeasurement : Bool
    interpretation : String

canonicalCravingCausalCompetitionBoundary : CravingCausalCompetitionBoundary
canonicalCravingCausalCompetitionBoundary = record
  { appetiteBoundary = Microbiome.canonicalMicrobiomeHostAppetiteBoundary
  ; hiddenStateBoundary = Hidden.canonicalNonrecurrenceBoundary
  ; cravingMayReflectDeficiency = true
  ; cravingReliablyDiagnosesDeficiency = false
  ; cravingMayReflectMicrobialInfluence = true
  ; cravingIsMicrobialCommand = false
  ; oneBehaviourMayHaveMultipleInternalCauses = true
  ; clinicalInferenceBlockedWithoutMeasurement = true
  ; interpretation = "A craving is an underdetermined behavioural boundary event compatible with nutrient need, microbial signalling, endocrine state, learned association, reward, stress, disease and availability; causal attribution requires discriminating measurements and interventions"
  }
