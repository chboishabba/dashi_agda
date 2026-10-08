module DASHI.Cognition.ClinicToStreetsCausalProvenanceRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Data.Empty using (⊥)

import DASHI.Cognition.ClinicToStreetsCausalProvenanceExact as CTS
import DASHI.Cognition.CognitiveWarfarePlatoTraumaDetectorWeldExact as Detector

fullContextStructuralVisible :
  CTS.ProvenanceVisibility.structuralVisible CTS.fullContext ≡ true
fullContextStructuralVisible = refl

atomisedStructuralHidden :
  CTS.ProvenanceVisibility.structuralVisible CTS.atomisedContext ≡ false
atomisedStructuralHidden = refl

atomisedIntimateRetained :
  CTS.ProvenanceVisibility.intimateVisible CTS.atomisedContext ≡ true
atomisedIntimateRetained = refl

atomisedIntrapsychicRetained :
  CTS.ProvenanceVisibility.intrapsychicVisible CTS.atomisedContext ≡ true
atomisedIntrapsychicRetained = refl

atomisingErasureWitness :
  CTS.CausalProvenanceErasure CTS.fullContext CTS.atomisedContext
atomisingErasureWitness = CTS.canonicalAtomisingErasure

psychicEffectIntentFirewall :
  CTS.PsychicEffectImpliesEstablishedIntent → ⊥
psychicEffectIntentFirewall = CTS.psychicEffectDoesNotEstablishIntent

therapyEssenceFirewall :
  CTS.EffectSignatureImpliesTherapyEssence → ⊥
therapyEssenceFirewall = CTS.effectSignatureDoesNotEstablishTherapyEssence

coneInfluenceFirewall :
  Detector.ConeDeformationImpliesInfluence → ⊥
coneInfluenceFirewall = CTS.coneDeformationStillDoesNotEstablishInfluence

provenanceTruthFirewall :
  Detector.ProvenanceImpliesTruth → ⊥
provenanceTruthFirewall = CTS.provenanceStillDoesNotEstablishTruth
