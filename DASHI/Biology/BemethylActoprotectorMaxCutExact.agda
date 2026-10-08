module DASHI.Biology.BemethylActoprotectorMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BemethylActoprotectorClaimAtlasExact as Claims
import DASHI.Biology.BemethylMetabolicMechanismBoundaryExact as Mechanism
import DASHI.Biology.BemethylBioenergeticCrossPollinationExact as Weld
import DASHI.Biology.BemethylHumanEvidenceAcquisitionExact as Human
import DASHI.Biology.BemethylParetoSnowballExact as Pareto

record BemethylMaxCut : Set where
  field
    atlas : Claims.BemethylClaimAtlas
    metabolicBoundary : Mechanism.MechanismBoundary
    bioenergeticWeld : Weld.BemethylBioenergeticWeld
    humanEvidence : Human.HumanEvidenceAcquisition
    paretoSnowball : Pareto.ParetoSnowball

    transcriptFormalised : Bool
    historicalReviewCrossChecked : Bool
    metabolismLiteratureCrossChecked : Bool
    controlledHumanHeatEvidenceAcquired : Bool
    humanExposureEvidenceAcquired : Bool
    humanDiseaseContextMechanismEvidenceAcquired : Bool

    modernMechanismTargetIdentified : Bool
    directGenomeBindingReceiptPaid : Bool
    modernHumanPerformanceReplicationPaid : Bool
    humanAntimutagenicOutcomePaid : Bool
    doseResponseSameObjectPaid : Bool
    exposureEfficacySameObjectPaid : Bool
    oxygenHeatIndependenceModernReplicationPaid : Bool
    clinicalRecommendationPaid : Bool

    nextEmpiricalCut : String

open BemethylMaxCut public

canonicalBemethylMaxCut : BemethylMaxCut
canonicalBemethylMaxCut = record
  { atlas = Claims.canonicalBemethylClaimAtlas
  ; metabolicBoundary = Mechanism.mitochondrialBoundary
  ; bioenergeticWeld = Weld.canonicalBemethylBioenergeticWeld
  ; humanEvidence = Human.canonicalHumanEvidenceAcquisition
  ; paretoSnowball = Pareto.canonicalParetoSnowball
  ; transcriptFormalised = true
  ; historicalReviewCrossChecked = true
  ; metabolismLiteratureCrossChecked = true
  ; controlledHumanHeatEvidenceAcquired = true
  ; humanExposureEvidenceAcquired = true
  ; humanDiseaseContextMechanismEvidenceAcquired = true
  ; modernMechanismTargetIdentified = false
  ; directGenomeBindingReceiptPaid = false
  ; modernHumanPerformanceReplicationPaid = false
  ; humanAntimutagenicOutcomePaid = false
  ; doseResponseSameObjectPaid = false
  ; exposureEfficacySameObjectPaid = false
  ; oxygenHeatIndependenceModernReplicationPaid = false
  ; clinicalRecommendationPaid = false
  ; nextEmpiricalCut = "Highest-value acquisition is direct molecular target engagement. Next is the original controlled performance literature with complete allocation/endpoints/exposure, followed by modern independent same-compound replication. Historical heat/exertion and human excretion evidence are now acquired but do not close modern replication or same-object exposure-efficacy."
  }

transcriptPaid : transcriptFormalised canonicalBemethylMaxCut ≡ true
transcriptPaid = refl

controlledHumanHeatPaid :
  controlledHumanHeatEvidenceAcquired canonicalBemethylMaxCut ≡ true
controlledHumanHeatPaid = refl

humanExposurePaid : humanExposureEvidenceAcquired canonicalBemethylMaxCut ≡ true
humanExposurePaid = refl

modernTargetOpen : modernMechanismTargetIdentified canonicalBemethylMaxCut ≡ false
modernTargetOpen = refl

modernHumanReplicationOpen :
  modernHumanPerformanceReplicationPaid canonicalBemethylMaxCut ≡ false
modernHumanReplicationOpen = refl

sameObjectExposureEfficacyOpen :
  exposureEfficacySameObjectPaid canonicalBemethylMaxCut ≡ false
sameObjectExposureEfficacyOpen = refl

clinicalRecommendationBlocked : clinicalRecommendationPaid canonicalBemethylMaxCut ≡ false
clinicalRecommendationBlocked = refl
