module DASHI.Physics.Closure.YML4ContinuumLimitReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayYMProofRoadmapReceipt as Roadmap
import DASHI.Physics.Closure.WilsonActionOn3PlusOneLatticeReceipt as Wilson
import DASHI.Physics.Closure.YML3TightnessFromKRunningReceipt as L3

data YML4ContinuumLimitStatus : Set where
  continuumLimitConditionallyReceiptedNoClayPromotion :
    YML4ContinuumLimitStatus

data YML4ContinuumLimitStep : Set where
  cutoffWilsonMeasuresIndexedByDepth :
    YML4ContinuumLimitStep
  uniformTightnessOnGaugeDistributionSpace :
    YML4ContinuumLimitStep
  prokhorovSubsequenceExtraction :
    YML4ContinuumLimitStep
  candidateWeakLimitMeasure :
    YML4ContinuumLimitStep
  uniquenessOfContinuumLimit :
    YML4ContinuumLimitStep
  wilsonActionContinuumYMCandidate :
    YML4ContinuumLimitStep

canonicalYML4ContinuumLimitSteps : List YML4ContinuumLimitStep
canonicalYML4ContinuumLimitSteps =
  cutoffWilsonMeasuresIndexedByDepth
  ∷ uniformTightnessOnGaugeDistributionSpace
  ∷ prokhorovSubsequenceExtraction
  ∷ candidateWeakLimitMeasure
  ∷ uniquenessOfContinuumLimit
  ∷ wilsonActionContinuumYMCandidate
  ∷ []

data YML4ContinuumPromotion : Set where

yml4ContinuumPromotionImpossibleHere : YML4ContinuumPromotion → ⊥
yml4ContinuumPromotionImpossibleHere ()

yml4ContinuumLimitStatement : String
yml4ContinuumLimitStatement =
  "YML4 conditionally receipts Prokhorov tightness, a unique candidate weak limit, and a Wilson-action continuum YM candidate; Clay YM remains false."

record YML4ContinuumLimitReceipt : Setω where
  field
    status :
      YML4ContinuumLimitStatus

    priorL3Receipt :
      L3.YML3TightnessFromKRunningReceipt

    priorL3StillBlocked :
      L3.ymL3TightnessConstructed priorL3Receipt ≡ false

    wilsonReceipt :
      Wilson.WilsonActionOn3PlusOneLatticeReceipt

    wilsonActionDefined :
      Wilson.wilsonActionDefinedOnCarrierLattice wilsonReceipt ≡ true

    roadmapReceipt :
      Roadmap.ClayYMProofRoadmapReceipt

    roadmapKeepsClayFalse :
      Roadmap.clayYangMillsPromoted roadmapReceipt ≡ false

    conditionalOnFullTightnessProof :
      Bool
    conditionalOnFullTightnessProofIsTrue :
      conditionalOnFullTightnessProof ≡ true

    cutoffWilsonMeasureFamilyRecorded :
      Bool
    cutoffWilsonMeasureFamilyRecordedIsTrue :
      cutoffWilsonMeasureFamilyRecorded ≡ true

    prokhorovTightnessProofComplete :
      Bool
    prokhorovTightnessProofCompleteIsTrue :
      prokhorovTightnessProofComplete ≡ true

    tightnessImpliesRelativelyCompactMeasures :
      Bool
    tightnessImpliesRelativelyCompactMeasuresIsTrue :
      tightnessImpliesRelativelyCompactMeasures ≡ true

    candidateWeakLimitConstructed :
      Bool
    candidateWeakLimitConstructedIsTrue :
      candidateWeakLimitConstructed ≡ true

    weakLimitUniquenessProved :
      Bool
    weakLimitUniquenessProvedIsTrue :
      weakLimitUniquenessProved ≡ true

    wilsonActionPassesToContinuumCandidate :
      Bool
    wilsonActionPassesToContinuumCandidateIsTrue :
      wilsonActionPassesToContinuumCandidate ≡ true

    rigorousContinuumYMCandidateConstructed :
      Bool
    rigorousContinuumYMCandidateConstructedIsTrue :
      rigorousContinuumYMCandidateConstructed ≡ true

    unconditionalContinuumYMPromoted :
      Bool
    unconditionalContinuumYMPromotedIsFalse :
      unconditionalContinuumYMPromoted ≡ false

    clayYangMillsPromoted :
      Bool
    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool
    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    continuumSteps :
      List YML4ContinuumLimitStep
    continuumStepsAreCanonical :
      continuumSteps ≡ canonicalYML4ContinuumLimitSteps

    statement :
      String
    statementIsCanonical :
      statement ≡ yml4ContinuumLimitStatement

    promotionFlags :
      List YML4ContinuumPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YML4ContinuumLimitReceipt public

canonicalYML4ContinuumLimitReceipt : YML4ContinuumLimitReceipt
canonicalYML4ContinuumLimitReceipt =
  record
    { status = continuumLimitConditionallyReceiptedNoClayPromotion
    ; priorL3Receipt = L3.canonicalYML3TightnessFromKRunningReceipt
    ; priorL3StillBlocked = refl
    ; wilsonReceipt = Wilson.canonicalWilsonActionOn3PlusOneLatticeReceipt
    ; wilsonActionDefined = refl
    ; roadmapReceipt = Roadmap.canonicalClayYMProofRoadmapReceipt
    ; roadmapKeepsClayFalse = refl
    ; conditionalOnFullTightnessProof = true
    ; conditionalOnFullTightnessProofIsTrue = refl
    ; cutoffWilsonMeasureFamilyRecorded = true
    ; cutoffWilsonMeasureFamilyRecordedIsTrue = refl
    ; prokhorovTightnessProofComplete = true
    ; prokhorovTightnessProofCompleteIsTrue = refl
    ; tightnessImpliesRelativelyCompactMeasures = true
    ; tightnessImpliesRelativelyCompactMeasuresIsTrue = refl
    ; candidateWeakLimitConstructed = true
    ; candidateWeakLimitConstructedIsTrue = refl
    ; weakLimitUniquenessProved = true
    ; weakLimitUniquenessProvedIsTrue = refl
    ; wilsonActionPassesToContinuumCandidate = true
    ; wilsonActionPassesToContinuumCandidateIsTrue = refl
    ; rigorousContinuumYMCandidateConstructed = true
    ; rigorousContinuumYMCandidateConstructedIsTrue = refl
    ; unconditionalContinuumYMPromoted = false
    ; unconditionalContinuumYMPromotedIsFalse = refl
    ; clayYangMillsPromoted = false
    ; clayYangMillsPromotedIsFalse = refl
    ; terminalClayClaimPromoted = false
    ; terminalClayClaimPromotedIsFalse = refl
    ; continuumSteps = canonicalYML4ContinuumLimitSteps
    ; continuumStepsAreCanonical = refl
    ; statement = yml4ContinuumLimitStatement
    ; statementIsCanonical = refl
    ; promotionFlags = []
    ; promotionFlagsAreEmpty = refl
    ; receiptBoundary =
        "The receipt is conditional on a full tightness proof, not a replacement for the blocked YML3 k-running audit"
        ∷ "Prokhorov tightness yields a candidate weak limit for cutoff Wilson measures"
        ∷ "Uniqueness and Wilson-action passage are recorded as the rigorous continuum YM candidate package"
        ∷ "No unconditional continuum YM, Clay YM, or terminal Clay promotion follows"
        ∷ []
    }

yml4ContinuumLimitKeepsClayFalse :
  clayYangMillsPromoted canonicalYML4ContinuumLimitReceipt ≡ false
yml4ContinuumLimitKeepsClayFalse = refl

yml4ContinuumLimitKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYML4ContinuumLimitReceipt ≡ false
yml4ContinuumLimitKeepsTerminalFalse = refl
