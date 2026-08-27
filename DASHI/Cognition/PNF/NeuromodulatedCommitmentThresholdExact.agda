module DASHI.Cognition.PNF.NeuromodulatedCommitmentThresholdExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.BoundedEvidenceCommitmentExact as Evidence

------------------------------------------------------------------------
-- NEUROMODULATED COMMITMENT THRESHOLD
--
-- Literature calibration:
-- Gary Aston-Jones; Jonathan D. Cohen,
-- "An Integrative Theory of Locus Coeruleus-Norepinephrine Function:
-- Adaptive Gain and Optimal Performance",
-- DOI 10.1146/annurev.neuro.28.061604.135709.
--
-- Hongjie Xia; Maxime Maheu; Gary A. Kane; Benjamin B. Scott,
-- "Regulation of the decision threshold by the locus coeruleus",
-- DOI 10.1038/s41386-026-02399-x.
--
-- The 2026 study provides causal evidence in rats that LC-NE activation can
-- increase modeled decision thresholds.  The exact finite policy below is a
-- calibration model, not a quantitative receptor/LC firing-rate fit and not a
-- universal stress law.
------------------------------------------------------------------------

data ThresholdPolicy : Set where lowerThreshold elevatedThreshold : ThresholdPolicy

thresholdUnder : ThresholdPolicy → Evidence.EvidenceLevel → Evidence.ThresholdCommitment
thresholdUnder lowerThreshold Evidence.e0 = Evidence.stillDeliberating
thresholdUnder lowerThreshold Evidence.e1 = Evidence.committed
thresholdUnder lowerThreshold Evidence.e2 = Evidence.committed
thresholdUnder elevatedThreshold Evidence.e0 = Evidence.stillDeliberating
thresholdUnder elevatedThreshold Evidence.e1 = Evidence.stillDeliberating
thresholdUnder elevatedThreshold Evidence.e2 = Evidence.committed

sameEvidenceDifferentThresholdChangesCommitment :
  thresholdUnder lowerThreshold Evidence.e1
  ≡ thresholdUnder elevatedThreshold Evidence.e1 → ⊥
sameEvidenceDifferentThresholdChangesCommitment ()

data LCNERegime : Set where baselineLC activatedLC : LCNERegime

candidatePolicyFromLC : LCNERegime → ThresholdPolicy
candidatePolicyFromLC baselineLC = lowerThreshold
candidatePolicyFromLC activatedLC = elevatedThreshold

activatedLCCandidateRaisesFiniteThreshold :
  candidatePolicyFromLC activatedLC ≡ elevatedThreshold
activatedLCCandidateRaisesFiniteThreshold = refl

sameAccumulatedEvidenceLCStateMatters :
  thresholdUnder (candidatePolicyFromLC baselineLC) Evidence.e1
  ≡ thresholdUnder (candidatePolicyFromLC activatedLC) Evidence.e1 → ⊥
sameAccumulatedEvidenceLCStateMatters ()

record NeuromodulatedThresholdBoundary : Set where
  constructor neuromodulatedThresholdBoundary
  field
    accumulatedEvidenceDeterminesThreshold : Bool
    lcActivationAlwaysMeansStress : Bool
    lcActivationAlwaysRaisesThresholdInEveryTaskOrSpecies : Bool
    alpha2MechanismFullyLocalizedByFiniteModel : Bool

canonicalNeuromodulatedThresholdBoundary : NeuromodulatedThresholdBoundary
canonicalNeuromodulatedThresholdBoundary =
  neuromodulatedThresholdBoundary false false false false
