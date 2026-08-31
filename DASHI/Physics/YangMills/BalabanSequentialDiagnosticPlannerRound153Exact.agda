{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSequentialDiagnosticPlannerRound153Exact where

------------------------------------------------------------------------
-- ROUND153: ADAPTIVE DIAGNOSTICS REFINE THE SOURCE-REALIZATION FIBRE
--
-- Cross-pollinates the relational sequential experiment planner.  Candidate
-- source realizations can admit several diagnostic outcomes at finite cutoff /
-- volume / precision, so deterministic sensor semantics would be too strong.
--
-- Closing a sequential consumer means the requested SEARCH classification is
-- constant on the remaining candidate fibre.  It does not prove the physical
-- source equality and does not mark an Aristotle frontier leaf proved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Core.SequentialRelationalExperimentPlannerExact as Sequential
import DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact as R146
import DASHI.Physics.YangMills.BalabanFrontierExperimentDesignRound148Exact as R148

-- A source-diagnostic experiment is an experiment-design coordinate plus an
-- application-supplied probe reference/cost.  The coordinate role itself remains
-- owned by Round148.
record BalabanDiagnosticExperiment : Set where
  constructor balabanDiagnosticExperiment
  field
    coordinate : R148.BalabanFrontierCoordinate
    cost : Nat
    probeReference : String

open BalabanDiagnosticExperiment public

record BalabanSequentialDiagnosticProgramme : Set₂ where
  field
    CandidateRealization Observation Consumer : Set

    predicts : CandidateRealization →
      BalabanDiagnosticExperiment → Observation → Set

    observationReference : Observation → String

    system : Sequential.RelationalExperimentSystem
      CandidateRealization BalabanDiagnosticExperiment Observation
    systemUsesDeclaredPredictions : Sequential.predicts system ≡ predicts

    live : CandidateRealization → Set
    consumer : CandidateRealization → Consumer

    plan : Sequential.CertifiedSequentialRelationalPlan system consumer live

    -- Every experiment selected by the programme must diagnose one of the exact
    -- Round146 leaves; no untyped free-floating measurements enter this planner.
    experimentTargetsFrontierLeaf :
      BalabanDiagnosticExperiment → R146.BalabanFrontierLeaf
    experimentTargetIsCoordinateTarget : ∀ experiment →
      experimentTargetsFrontierLeaf experiment
      ≡ R148.coordinateTargetsLeaf (coordinate experiment)

    nuisanceControlReference : String
    sequentialPlanAuthorityReference : String

open BalabanSequentialDiagnosticProgramme public

canonicalDiagnosticSystem :
  ∀ {CandidateRealization Observation : Set} →
  (predicts : CandidateRealization → BalabanDiagnosticExperiment → Observation → Set) →
  (observationReference : Observation → String) →
  Sequential.RelationalExperimentSystem
    CandidateRealization BalabanDiagnosticExperiment Observation
canonicalDiagnosticSystem predicts observationReference =
  Sequential.relationalExperimentSystem
    predicts
    cost
    probeReference
    observationReference

record Round108DirectRouteDiagnosticProgramme : Set₂ where
  field
    programme : BalabanSequentialDiagnosticProgramme

    -- The main experiment coordinate is the current highest-alpha single source
    -- leaf.  Adaptive continuations may additionally inspect nuisance/systematic
    -- coordinates, but the declared consumer is about this direct route.
    directRound108Probe : BalabanDiagnosticExperiment
    directRound108ProbeTargetsMatch :
      R148.coordinate directRound108Probe ≡ R148.round108PotentialMatchResidual

open Round108DirectRouteDiagnosticProgramme public

record BalabanSequentialDiagnosticBoundary : Set where
  constructor balabanSequentialDiagnosticBoundary
  field
    nextProbeMayDependOnEarlierOutcome : Bool
    nextProbeMayDependOnEarlierOutcomeIsTrue :
      nextProbeMayDependOnEarlierOutcome ≡ true
    terminalSearchConsumerIdentifiesUniqueSourceRealization : Bool
    terminalSearchConsumerIdentifiesUniqueSourceRealizationIsFalse :
      terminalSearchConsumerIdentifiesUniqueSourceRealization ≡ false
    terminalSearchConsumerProvesSourceEquality : Bool
    terminalSearchConsumerProvesSourceEqualityIsFalse :
      terminalSearchConsumerProvesSourceEquality ≡ false

canonicalBalabanSequentialDiagnosticBoundary : BalabanSequentialDiagnosticBoundary
canonicalBalabanSequentialDiagnosticBoundary =
  balabanSequentialDiagnosticBoundary true refl false refl false refl

balabanSequentialDiagnosticPlannerLevel : ProofLevel
balabanSequentialDiagnosticPlannerLevel = machineChecked
