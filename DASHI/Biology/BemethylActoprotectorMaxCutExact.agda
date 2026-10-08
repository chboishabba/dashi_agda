module DASHI.Biology.BemethylActoprotectorMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BemethylActoprotectorClaimAtlasExact as Claims
import DASHI.Biology.BemethylMetabolicMechanismBoundaryExact as Mechanism
import DASHI.Biology.BemethylMechanismInterventionAcquisitionExact as Intervention
import DASHI.Biology.BemethylModernAthleteReplicationExact as ModernAthlete
import DASHI.Biology.BemethylBioenergeticCrossPollinationExact as Weld
import DASHI.Biology.BemethylHumanEvidenceAcquisitionExact as Human
import DASHI.Biology.BemethylParetoSnowballExact as Pareto

record BemethylMaxCut : Set where
  field
    atlas : Claims.BemethylClaimAtlas
    metabolicBoundary : Mechanism.MechanismBoundary
    mechanismIntervention : Intervention.MechanismInterventionAcquisition
    modernAthleteEvidence : ModernAthlete.ModernAthleteReplication
    bioenergeticWeld : Weld.BemethylBioenergeticWeld
    humanEvidence : Human.HumanEvidenceAcquisition
    paretoSnowball : Pareto.ParetoSnowball

    transcriptFormalised : Bool
    historicalReviewCrossChecked : Bool
    metabolismLiteratureCrossChecked : Bool
    controlledHumanHeatEvidenceAcquired : Bool
    historicalControlledPerformanceEvidenceAcquired : Bool
    modernRandomizedAthleteEvidenceAcquired : Bool
    modernDirectBetweenGroupEffectPaid : Bool
    independentExternalPerformanceReplicationPaid : Bool
    humanExposureEvidenceAcquired : Bool
    humanPKParameterEvidenceAcquired : Bool
    humanDiseaseContextMechanismEvidenceAcquired : Bool
    transcriptionDependentMechanismEvidenceAcquired : Bool

    modernMechanismTargetIdentified : Bool
    directGenomeBindingReceiptPaid : Bool
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
  ; modernAthleteEvidence = ModernAthlete.canonicalModernAthleteReplication
  ; bioenergeticWeld = Weld.canonicalBemethylBioenergeticWeld
  ; humanEvidence = Human.canonicalHumanEvidenceAcquisition
  ; paretoSnowball = Pareto.canonicalParetoSnowball
  ; transcriptFormalised = true
  ; historicalReviewCrossChecked = true
  ; metabolismLiteratureCrossChecked = true
  ; controlledHumanHeatEvidenceAcquired = true
  ; historicalControlledPerformanceEvidenceAcquired = true
  ; modernRandomizedAthleteEvidenceAcquired = true
  ; modernDirectBetweenGroupEffectPaid = false
  ; independentExternalPerformanceReplicationPaid = false
  ; humanExposureEvidenceAcquired = true
  ; humanPKParameterEvidenceAcquired = true
  ; humanDiseaseContextMechanismEvidenceAcquired = true
  ; transcriptionDependentMechanismEvidenceAcquired = true
  ; modernMechanismTargetIdentified = false
  ; directGenomeBindingReceiptPaid = false
  ; humanAntimutagenicOutcomePaid = false
  ; doseResponseSameObjectPaid = false
  ; exposureEfficacySameObjectPaid = false
  ; oxygenHeatIndependenceModernReplicationPaid = false
  ; clinicalRecommendationPaid = false
  ; nextEmpiricalCut = "The 2023 randomized double-blind placebo-controlled athlete study now pays modern same-compound evidence, but the recovered surface does not yet pay a direct Metaprot-vs-placebo effect estimate, participant-level exposure coupling, or independent external replication. Direct molecular target engagement remains the highest-value mechanism cut."
  }

transcriptPaid : transcriptFormalised canonicalBemethylMaxCut ≡ true
transcriptPaid = refl

controlledHumanHeatPaid :
  controlledHumanHeatEvidenceAcquired canonicalBemethylMaxCut ≡ true
controlledHumanHeatPaid = refl

historicalPerformancePaid :
  historicalControlledPerformanceEvidenceAcquired canonicalBemethylMaxCut ≡ true
historicalPerformancePaid = refl

modernRandomizedAthletePaid :
  modernRandomizedAthleteEvidenceAcquired canonicalBemethylMaxCut ≡ true
modernRandomizedAthletePaid = refl

directModernBetweenGroupEffectOpen :
  modernDirectBetweenGroupEffectPaid canonicalBemethylMaxCut ≡ false
directModernBetweenGroupEffectOpen = refl

independentExternalReplicationOpen :
  independentExternalPerformanceReplicationPaid canonicalBemethylMaxCut ≡ false
independentExternalReplicationOpen = refl

humanExposurePaid : humanExposureEvidenceAcquired canonicalBemethylMaxCut ≡ true
humanExposurePaid = refl

humanPKParameterPaid : humanPKParameterEvidenceAcquired canonicalBemethylMaxCut ≡ true
humanPKParameterPaid = refl

transcriptionDependencePaid :
  transcriptionDependentMechanismEvidenceAcquired canonicalBemethylMaxCut ≡ true
transcriptionDependencePaid = refl

modernTargetOpen : modernMechanismTargetIdentified canonicalBemethylMaxCut ≡ false
modernTargetOpen = refl

sameObjectExposureEfficacyOpen :
  exposureEfficacySameObjectPaid canonicalBemethylMaxCut ≡ false
sameObjectExposureEfficacyOpen = refl

clinicalRecommendationBlocked : clinicalRecommendationPaid canonicalBemethylMaxCut ≡ false
clinicalRecommendationBlocked = refl
