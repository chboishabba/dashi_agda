module DASHI.Cognition.OracleEllisonCognitiveWarfareWeldExact where

------------------------------------------------------------------------
-- CASE-SPECIFIC WELD TO EXISTING COGNITIVE-WARFARE DETECTOR MACHINERY
--
-- Reuses the existing theorem boundary rather than replacing it:
-- provenance can refine an origin query, but provenance != truth;
-- cone deformation != hostile influence; content equality != common controller.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.CognitiveWarfareAdmissibleDetectionExact as Detection
import DASHI.Cognition.CognitiveWarfarePlatoTraumaDetectorWeldExact as Existing
import DASHI.Cognition.OracleEllisonChinaIsraelComparativeFibreExact as Compare

------------------------------------------------------------------------
-- Literal reuse pins.
------------------------------------------------------------------------

existingProvenanceCanStrictlyRefine :
  Existing.CognitiveDetectorWeldBoundary.addingProvenanceCanStrictlyRefine
    Existing.canonicalCognitiveDetectorWeldBoundary
  ≡ true
existingProvenanceCanStrictlyRefine = refl

existingProvenanceDoesNotImplyTruth :
  Existing.CognitiveDetectorWeldBoundary.provenanceImpliesTruth
    Existing.canonicalCognitiveDetectorWeldBoundary
  ≡ false
existingProvenanceDoesNotImplyTruth = refl

existingConeDoesNotImplyHostileInfluence :
  Existing.CognitiveDetectorWeldBoundary.coneDeformationImpliesHostileInfluence
    Existing.canonicalCognitiveDetectorWeldBoundary
  ≡ false
existingConeDoesNotImplyHostileInfluence = refl

------------------------------------------------------------------------
-- Case interpretation.
------------------------------------------------------------------------

provenancePaysTruth : Bool
provenancePaysTruth = false

vendorIdentityPaysCommonController : Bool
vendorIdentityPaysCommonController = false

operationalIntegrationPaysPoliticalMotive : Bool
operationalIntegrationPaysPoliticalMotive = false

sharedSecurityFunctionPaysCommonIdeology : Bool
sharedSecurityFunctionPaysCommonIdeology = false

provenanceCanRefineOriginQuery : Bool
provenanceCanRefineOriginQuery = true

institutionalGraphCanRefineDeploymentQuery : Bool
institutionalGraphCanRefineDeploymentQuery = true

record OracleEllisonDetectorBoundary : Set where
  constructor oracle-ellison-detector-boundary
  field
    provenanceUsefulForOrigin : Bool
    institutionUsefulForDeployment : Bool
    provenanceCreatesTruth : Bool
    vendorCreatesControllerIdentity : Bool
    integrationCreatesMotive : Bool
    sameFunctionCreatesCommonIdeology : Bool

canonicalOracleEllisonDetectorBoundary : OracleEllisonDetectorBoundary
canonicalOracleEllisonDetectorBoundary =
  oracle-ellison-detector-boundary
    true true false false false false
