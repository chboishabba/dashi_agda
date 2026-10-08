module DASHI.Biology.BemethylActoprotectorMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BemethylActoprotectorClaimAtlasExact as Claims
import DASHI.Biology.BemethylMetabolicMechanismBoundaryExact as Mechanism
import DASHI.Biology.BemethylBioenergeticCrossPollinationExact as Weld

record BemethylMaxCut : Set where
  field
    atlas : Claims.BemethylClaimAtlas
    metabolicBoundary : Mechanism.MechanismBoundary
    bioenergeticWeld : Weld.BemethylBioenergeticWeld

    transcriptFormalised : Bool
    historicalReviewCrossChecked : Bool
    metabolismLiteratureCrossChecked : Bool

    modernMechanismTargetIdentified : Bool
    directGenomeBindingReceiptPaid : Bool
    modernHumanPerformanceReplicationPaid : Bool
    humanAntimutagenicOutcomePaid : Bool
    doseResponseSameObjectPaid : Bool
    oxygenHeatIndependenceModernReplicationPaid : Bool
    clinicalRecommendationPaid : Bool

    nextEmpiricalCut : String

open BemethylMaxCut public

canonicalBemethylMaxCut : BemethylMaxCut
canonicalBemethylMaxCut = record
  { atlas = Claims.canonicalBemethylClaimAtlas
  ; metabolicBoundary = Mechanism.mitochondrialBoundary
  ; bioenergeticWeld = Weld.canonicalBemethylBioenergeticWeld
  ; transcriptFormalised = true
  ; historicalReviewCrossChecked = true
  ; metabolismLiteratureCrossChecked = true
  ; modernMechanismTargetIdentified = false
  ; directGenomeBindingReceiptPaid = false
  ; modernHumanPerformanceReplicationPaid = false
  ; humanAntimutagenicOutcomePaid = false
  ; doseResponseSameObjectPaid = false
  ; oxygenHeatIndependenceModernReplicationPaid = false
  ; clinicalRecommendationPaid = false
  ; nextEmpiricalCut = "Identify a molecular target with target-engagement evidence; then reproduce metabolic, oxygen/heat and performance effects in a modern controlled human protocol on the same exposure-calibrated compound"
  }

transcriptPaid : transcriptFormalised canonicalBemethylMaxCut ≡ true
transcriptPaid = refl

modernTargetOpen : modernMechanismTargetIdentified canonicalBemethylMaxCut ≡ false
modernTargetOpen = refl

modernHumanReplicationOpen :
  modernHumanPerformanceReplicationPaid canonicalBemethylMaxCut ≡ false
modernHumanReplicationOpen = refl

clinicalRecommendationBlocked : clinicalRecommendationPaid canonicalBemethylMaxCut ≡ false
clinicalRecommendationBlocked = refl
