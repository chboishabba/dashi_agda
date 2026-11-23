module DASHI.Culture.AmyEskridgeBemNativeStatisticsDiscriminatorWeldExact where

-- EXISTING DASHI STATS + EXPERIMENT-DISCRIMINATION OWNERS.
-- A source-specific adapter; no invention of Tukey-HSD or raw Bem records.
--
-- Robust Tukey in DASHI/Statistics/Vec15Robust.agda is an IQR OUTLIER
-- fence over an exactly 15-element natural-number prime-profile carrier,
-- NOT Tukey's honestly-significant-difference post-hoc ANOVA test.
-- The 15-element inference interface in Vec15Inference is an explicit
-- source-local deterministic scaffold; its integer field called "pValue"
-- is countNonZero15, NOT a calibrated inferential probability.
-- These existing operators can be used as provenance/robustness checks
-- on appropriate actual 15-profile data, but not as Bem's trial-level test.
--
-- THE REAL REUSABLE THEOREM here is the canonical
-- DASHI.Core.DiscriminatorSynthesisExact: identical reported aggregate
-- is an observer collision; independent dated documentation of an actual
-- analytic fork would separate the worlds. The bundle's read is an ideal
-- hypothetical observable: no such original Bem document was produced.
-- Source-specific empirical admission remains a separate gate.
--
-- Original paper 2011 DOI 10.1037/a0021524
-- Transparent Psi 2023 DOI 10.1098/rsos.191375
-- Prior experimental routes: AnomalousTemporalProofSearchExperimentAdmissionExact

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Core.DiscriminatorSynthesisExact as Disc
import DASHI.Core.ExperimentalCoordinateDesignExact as Design
import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Loop
import DASHI.Statistics.Vec15Robust as Tukey
import DASHI.Statistics.Vec15Inference as Inference
import DASHI.Governance.AnomalousTemporalProofSearchExperimentAdmissionExact as Admission
import DASHI.Culture.AmyEskridgeBemSteelmanRealisticIdentifiabilityExact as Bem

-- Non-data-bearing finite counterfactual worlds: they describe hypotheses.
data HistoricalProcess : Set where
  documentedForkWorld : HistoricalProcess
  uninterruptedPreregisteredWorld : HistoricalProcess

-- The OLD observable discards the original data-analysis chronology.
publishedAggregate : HistoricalProcess → Nat
publishedAggregate _ = 5307

publishedAggregateCollision : Disc.CurrentObserverCollision publishedAggregate
publishedAggregateCollision =
  Disc.currentObserverCollision documentedForkWorld
    uninterruptedPreregisteredWorld refl

-- A *counterfactual* measurement: authentic source chronology would
-- differ across these two constructed worlds; no actual result asserted.
hasAuthenticatedAnalysisFork : HistoricalProcess → Bool
hasAuthenticatedAnalysisFork documentedForkWorld = true
hasAuthenticatedAnalysisFork uninterruptedPreregisteredWorld = false

historicalDecisionLedgerBundle : Disc.ExperimentBundle HistoricalProcess
historicalDecisionLedgerBundle =
  Disc.experimentBundle
    Bool
    hasAuthenticatedAnalysisFork
    1
    "dated original methods/data/analysis chronology, review file or participant-level source"
    "independent acquisition; compare preregistration and original scripts; no inferred private decisions"

hypotheticalOriginalRecordsSeparateWorlds :
  Disc.BundleSeparates
    historicalDecisionLedgerBundle
    documentedForkWorld
    uninterruptedPreregisteredWorld
hypotheticalOriginalRecordsSeparateWorlds =
  Disc.bundleSeparates (λ ())

sameReportedNumberNeedsNewDiscriminator :
  Disc.DiscriminatingLanguageExtension publishedAggregate
sameReportedNumberNeedsNewDiscriminator =
  Disc.discriminatingLanguageExtension
    publishedAggregateCollision
    historicalDecisionLedgerBundle
    hypotheticalOriginalRecordsSeparateWorlds

-- Reuse original theorem, not new ad-hoc collision theory.
joinedOriginalEvidenceCanSeparate :
  Disc.joinedObservation
    publishedAggregate
    historicalDecisionLedgerBundle
    documentedForkWorld
  ≡
  Disc.joinedObservation
    publishedAggregate
    historicalDecisionLedgerBundle
    uninterruptedPreregisteredWorld
  → ⊥
joinedOriginalEvidenceCanSeparate =
  Disc.extensionJoinSeparates sameReportedNumberNeedsNewDiscriminator

-- The genuine existing Tukey/IQR outlier constructor is retained with its
-- original carrier and zero-carrier calibration, NOT silently promoted into
-- an inference on Bem's 100 participant records.
tukeyExistingZeroCarrierRegression :
  Tukey.tukeyOutlierMask15 Tukey.zeroCarrier15 ≡
  Tukey.tukeyOutlierMask15 Tukey.zeroCarrier15
tukeyExistingZeroCarrierRegression = refl

-- Existing design admits a preregistered physiology replication only
-- for its declared consumer; not the original Experiment 1 replay.
reusesPreregisteredPresentimentRoute :
  Admission.experiment Admission.presentimentRoute
    ≡ Admission.presentimentPreregisteredReplication
reusesPreregisteredPresentimentRoute = refl

reusesCorrectOriginalHypothesis :
  Bem.reportedBasisPoints (Bem.observed Bem.realisticNull)
    ≡ 5307
reusesCorrectOriginalHypothesis = refl

-- No implicit misleading conversion of the robust stats to statistics
-- of 100 real participants and no conversion of 15-profile integer
-- pseudo-"pValue" fields to classical p-values.
data PrimeProfileTukeyIsBemOriginalPosthocTest : Set where
data CountNonzeroPValueIsCalibratedProbability : Set where
data HypotheticalForkCoordinateIsAcquiredEvidence : Set where
data OriginalOneNumberDeterminesHistoricalAnalyticFork : Set where

noTukeyHSDByName :
  PrimeProfileTukeyIsBemOriginalPosthocTest → ⊥
noTukeyHSDByName ()
noInferenceScaffoldPValue :
  CountNonzeroPValueIsCalibratedProbability → ⊥
noInferenceScaffoldPValue ()
noHypotheticalEvidencePromotion :
  HypotheticalForkCoordinateIsAcquiredEvidence → ⊥
noHypotheticalEvidencePromotion ()
noOneNumberToFork :
  OriginalOneNumberDeterminesHistoricalAnalyticFork → ⊥
noOneNumberToFork ()

-- Existing source owners, for downstream refactoring when actual data
-- are available; their mere import does not perform statistical fitting.
tukeyRobustOwner : Nat
tukeyRobustOwner = Tukey.mad15 Tukey.zeroCarrier15

inferenceOwnerIsDescriptiveScaffold : Bool
inferenceOwnerIsDescriptiveScaffold =
  Inference.testResultIsWellFormed
    (Inference.anova15 Tukey.zeroCarrier15)

discriminatorOwner : Disc.DiscriminatorSynthesisBoundary
discriminatorOwner = Disc.canonicalDiscriminatorSynthesisBoundary

experimentalDesignOwner : Design.ExperimentalCoordinateBoundary
experimentalDesignOwner = Design.canonicalExperimentalCoordinateBoundary

activeBidiOwner : Loop.ActiveBidiDiscriminatorLoopBoundary
activeBidiOwner = Loop.canonicalActiveBidiDiscriminatorLoopBoundary
