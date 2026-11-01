module DASHI.Crypto.AdaptiveObservationTrajectoryResidueExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.TrajectoryResidueExact as Residue
import DASHI.Crypto.ChosenCiphertextObservationRefinementExact as Obs
import DASHI.Crypto.AlgorithmRelativeRecoveryCostExact as Cost
import DASHI.Crypto.ComputationalCandidateFibreExact as Candidate

------------------------------------------------------------------------
-- ADAPTIVE CRYPTO OBSERVATION AS HISTORY-BEARING TRANSCRIPT
--
-- Existing crypto owners already prove that observations can refine a live
-- candidate fibre without recovering the hidden state, and that cardinality
-- shrinkage need not reduce algorithm-relative recovery cost.  This adapter
-- adds the temporal statement: the transcript itself is retained path residue.
------------------------------------------------------------------------

Transcript : Obs.ObservationSystem → Set
Transcript system = List (Obs.ObservationSample system)

data TranscriptStep
    (system : Obs.ObservationSystem) :
    Transcript system → Transcript system → Set where
  recordSample :
    ∀ {transcript} (sample : Obs.ObservationSample system) →
    TranscriptStep system transcript (sample ∷ transcript)

transcriptResidue :
  ∀ {system : Obs.ObservationSystem} →
  Transcript system → Residue.ResidueFlag
transcriptResidue [] = Residue.residueAbsent
transcriptResidue (_ ∷ _) = Residue.residuePresent

transcriptStepCannotEraseObservationResidue :
  ∀ {system}
    {before after : Transcript system} →
  TranscriptStep system before after →
  transcriptResidue before ≡ Residue.residuePresent →
  transcriptResidue after ≡ Residue.residuePresent
transcriptStepCannotEraseObservationResidue (recordSample sample) present = refl

transcriptNoErasure :
  ∀ {system : Obs.ObservationSystem} →
  Residue.NoResidueErasure
    (TranscriptStep system)
    transcriptResidue
transcriptNoErasure = transcriptStepCannotEraseObservationResidue

oneObservationDepositsResidue :
  ∀ {system : Obs.ObservationSystem}
    (sample : Obs.ObservationSample system) →
  Residue.ResidueDeposition
    (TranscriptStep system)
    transcriptResidue
oneObservationDepositsResidue sample =
  Residue.residueDeposition
    []
    (sample ∷ [])
    (Residue.traceStep (recordSample sample) Residue.traceRefl)
    refl
    refl

------------------------------------------------------------------------
-- The existing monotone candidate-fibre theorem lifts directly to transcript
-- extension: consistency after the new observation implies consistency before.
------------------------------------------------------------------------

candidateConsistencyRefinesWithRecordedSample :
  ∀ {system : Obs.ObservationSystem}
    {candidate : Obs.Hidden system}
    {sample : Obs.ObservationSample system}
    {transcript : Transcript system} →
  Obs.ConsistentWith system candidate (sample ∷ transcript) →
  Obs.ConsistentWith system candidate transcript
candidateConsistencyRefinesWithRecordedSample = Obs.refinementIsMonotone

------------------------------------------------------------------------
-- Boundaries inherited from the existing crypto lane.
------------------------------------------------------------------------

record AdaptiveObservationTrajectoryBoundary : Set where
  constructor adaptiveObservationTrajectoryBoundary
  field
    recordedObservationHistoryCanPersist : Bool
    recordedObservationHistoryCanPersistIsTrue :
      recordedObservationHistoryCanPersist ≡ true
    transcriptRefinementMeansExactSecretRecovery : Bool
    transcriptRefinementMeansExactSecretRecoveryIsFalse :
      transcriptRefinementMeansExactSecretRecovery ≡ false
    candidateShrinkMeansAlgorithmicCostDrop : Bool
    candidateShrinkMeansAlgorithmicCostDropIsFalse :
      candidateShrinkMeansAlgorithmicCostDrop ≡ false
    plausibleCandidateMeansExactPreimage : Bool
    plausibleCandidateMeansExactPreimageIsFalse :
      plausibleCandidateMeansExactPreimage ≡ false

canonicalAdaptiveObservationTrajectoryBoundary :
  AdaptiveObservationTrajectoryBoundary
canonicalAdaptiveObservationTrajectoryBoundary =
  adaptiveObservationTrajectoryBoundary
    true refl
    false refl
    false refl
    false refl
