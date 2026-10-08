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
    historicalControlledPerformanceEvidenceAcquired : Bool
    humanExposureEvidenceAcquired : Bool
    humanPKParameterEvidenceAcquired : Bool
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
  ; historicalControlledPerformanceEvidenceAcquired = true
  ; humanExposureEvidenceAcquired = true
  ; humanPKParameterEvidenceAcquired = true
  ; humanDiseaseContextMechanismEvidenceAcquired = true
  ; modernMechanismTargetIdentified = false
  ; directGenomeBindingReceiptPaid = false
  ; modernHumanPerformanceReplicationPaid = false
  ; humanAntimutagenicOutcomePaid = false
  ; doseResponseSameObjectPaid = false
  ; exposureEfficacySameObjectPaid = false
  ; oxygenHeatIndependenceModernReplicationPaid = false
  ; clinicalRecommendationPaid = false
  ; nextEmpiricalCut = "The historical controlled operator-performance, controlled heat/exertion, healthy-volunteer pharmacokinetic, and excretion leaves are now source-paid at indexed-abstract level. The highest-value remaining acquisition is direct molecular target engagement; next recover full original methods/exposure for the historical trials and obtain a modern independent same-compound replication with efficacy and exposure measured on the same participants."
  }

transcriptPaid : transcriptFormalised canonicalBemethylMaxCut ≡ true
transcriptPaid = refl

controlledHumanHeatPaid :
  controlledHumanHeatEvidenceAcquired canonicalBemethylMaxCut ≡ true
controlledHumanHeatPaid = refl

historicalPerformancePaid :
  historicalControlledPerformanceEvidenceAcquired canonicalBemethylMaxCut ≡ true
historicalPerformancePaid = refl

humanExposurePaid : humanExposureEvidenceAcquired canonicalBemethylMaxCut ≡ true
humanExposurePaid = refl

humanPKParameterPaid : humanPKParameterEvidenceAcquired canonicalBemethylMaxCut ≡ true
humanPKParameterPaid = refl

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
