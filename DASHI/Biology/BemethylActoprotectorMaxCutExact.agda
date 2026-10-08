module DASHI.Biology.BemethylActoprotectorMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BemethylActoprotectorClaimAtlasExact as Claims
import DASHI.Biology.BemethylMetabolicMechanismBoundaryExact as Mechanism
import DASHI.Biology.BemethylMechanismInterventionAcquisitionExact as Intervention
import DASHI.Biology.BemethylBioenergeticCrossPollinationExact as Weld
import DASHI.Biology.BemethylHumanEvidenceAcquisitionExact as Human
import DASHI.Biology.BemethylParetoSnowballExact as Pareto

record BemethylMaxCut : Set where
  field
    atlas : Claims.BemethylClaimAtlas
    metabolicBoundary : Mechanism.MechanismBoundary
    mechanismIntervention : Intervention.MechanismInterventionAcquisition
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
    transcriptionDependentMechanismEvidenceAcquired : Bool

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
  ; mechanismIntervention = Intervention.canonicalMechanismInterventionAcquisition
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
  ; transcriptionDependentMechanismEvidenceAcquired = true
  ; modernMechanismTargetIdentified = false
  ; directGenomeBindingReceiptPaid = false
  ; modernHumanPerformanceReplicationPaid = false
  ; humanAntimutagenicOutcomePaid = false
  ; doseResponseSameObjectPaid = false
  ; exposureEfficacySameObjectPaid = false
  ; oxygenHeatIndependenceModernReplicationPaid = false
  ; clinicalRecommendationPaid = false
  ; nextEmpiricalCut = "Historical controlled operator-performance, controlled heat/exertion, healthy-volunteer pharmacokinetic/excretion, disease-context mechanism, and transcription-dependent rat antioxidant evidence are now source-paid at the indexed level. The irreducible mechanism leaf is direct bemethyl target engagement; then recover complete original methods/exposure and obtain modern independent same-compound replication with efficacy and exposure measured on the same participants."
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

transcriptionDependencePaid :
  transcriptionDependentMechanismEvidenceAcquired canonicalBemethylMaxCut ≡ true
transcriptionDependencePaid = refl

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
