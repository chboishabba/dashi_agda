module DASHI.Biology.Physical.BiologicalAtomicMolecularHammingReuseExact where

-- Round-23 cross-layer reuse.  An atom/molecule description and a code-space
-- mutation metric may accompany a source-qualified biological history.
-- Neither a chemistry source label nor a Hamming distance establishes a
-- phenotype transition, physical kinetics, or experimental equivalence.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
import Agda.Builtin.Nat
import DASHI.Biology.Physical.SourceIndexedBiologicalCarrierExact as Biology
import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Finite
import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Crypto.GrayPathTransitionOptimalExact as Gray
import DASHI.Chemistry.ExistingContentBridge as Existing
import DASHI.Biology.Molecular.MolecularConstrainedMinimizerBridge as Molecular

record CandidateMolecularHistory : Set where
  constructor candidateMolecularHistory
  field
    frame : Biology.FiniteDevelopmentalFrame
    proposedSpecies : Chemistry.Species
    proposedTransition : Chemistry.Transition
    candidateEvidence : Chemistry.EvidenceStatus
    chemicalSource : String
    codeBefore : Gray.Bit2
    codeAfter : Gray.Bit2
open CandidateMolecularHistory public

-- This is explicitly the *representation* metric of Gray's existing
-- two-bit carrier, not the 9-base Hamming metric of the measured dmsC RNA.
candidateCodeDistance : CandidateMolecularHistory → Agda.Builtin.Nat.Nat
candidateCodeDistance candidate =
  Gray.hamming2 (codeBefore candidate) (codeAfter candidate)

-- Intervention advances the native source/time/history coordinate while
-- retaining the chemical assertion as an unpromoted candidate.
advanceCandidate :
  Finite.Intervention → CandidateMolecularHistory →
  CandidateMolecularHistory
advanceCandidate action candidate = record
  { frame = Biology.nextFiniteFrame action (frame candidate)
  ; proposedSpecies = proposedSpecies candidate
  ; proposedTransition = proposedTransition candidate
  ; candidateEvidence = candidateEvidence candidate
  ; chemicalSource = chemicalSource candidate
  ; codeBefore = codeBefore candidate
  ; codeAfter = codeAfter candidate
  }

candidateTimeAdvances :
  (action : Finite.Intervention) (candidate : CandidateMolecularHistory) →
  Biology.observationTime (frame (advanceCandidate action candidate))
    ≡ Agda.Builtin.Nat.suc (Biology.observationTime (frame candidate))
candidateTimeAdvances action candidate =
  Biology.frameTimeAdvances action (frame candidate)

candidateHammingUnchangedByHistoryStep :
  (action : Finite.Intervention) (candidate : CandidateMolecularHistory) →
  candidateCodeDistance (advanceCandidate action candidate)
    ≡ candidateCodeDistance candidate
candidateHammingUnchangedByHistoryStep action candidate = refl

candidateEvidenceUnchangedByHistoryStep :
  (action : Finite.Intervention) (candidate : CandidateMolecularHistory) →
  candidateEvidence (advanceCandidate action candidate)
    ≡ candidateEvidence candidate
candidateEvidenceUnchangedByHistoryStep action candidate = refl

-- Imported owner modules intentionally remain distinct: the molecular
-- constrained minimizer discharges geometric/chemical obligations only
-- when its witnesses are supplied; the quantitative bridge retains
-- stoichiometry, law, instrument and wet-lab authority separately.


------------------------------------------------------------------------
-- Source-pinned measured RNA transition with an independent history
-- coordinate. This never assigns the original bacterial assay to a
-- synthetic planarian treatment or claims its readout predicts morphology.
------------------------------------------------------------------------
import DASHI.Biology.Physical.OriginalDmscTwoGenotypeMeasuredExact as Dmsc
import DASHI.Biology.Physical.BiologicalRNA9HammingExact as RNAMetric

record OriginalRNA9PairAtHistory : Set where
  constructor originalRNA9PairAtHistory
  field
    developmentalFrame : Biology.FiniteDevelopmentalFrame
    measuredLeft : Dmsc.OriginalDmscMeasuredNineMer
    measuredRight : Dmsc.OriginalDmscMeasuredNineMer
    leftIsOriginal : measuredLeft ≡ Dmsc.originalOne
    rightIsOriginal : measuredRight ≡ Dmsc.originalTwo

canonicalOriginalPairAtHistory :
  Biology.FiniteDevelopmentalFrame → OriginalRNA9PairAtHistory
canonicalOriginalPairAtHistory historicalFrame =
  originalRNA9PairAtHistory historicalFrame
    Dmsc.originalOne Dmsc.originalTwo refl refl

advanceOriginalPairHistory :
  Finite.Intervention → OriginalRNA9PairAtHistory →
  OriginalRNA9PairAtHistory
advanceOriginalPairHistory action pair =
  originalRNA9PairAtHistory
    (Biology.nextFiniteFrame action
      (OriginalRNA9PairAtHistory.developmentalFrame pair))
    (OriginalRNA9PairAtHistory.measuredLeft pair)
    (OriginalRNA9PairAtHistory.measuredRight pair)
    (OriginalRNA9PairAtHistory.leftIsOriginal pair)
    (OriginalRNA9PairAtHistory.rightIsOriginal pair)

canonicalOriginalPairDistance :
  (historicalFrame : Biology.FiniteDevelopmentalFrame) →
  RNAMetric.hamming9
    (Dmsc.OriginalDmscMeasuredNineMer.genomeRNA
      (OriginalRNA9PairAtHistory.measuredLeft
        (canonicalOriginalPairAtHistory historicalFrame)))
    (Dmsc.OriginalDmscMeasuredNineMer.genomeRNA
      (OriginalRNA9PairAtHistory.measuredRight
        (canonicalOriginalPairAtHistory historicalFrame))) ≡ 1
canonicalOriginalPairDistance historicalFrame =
  RNAMetric.originalsOneSubstitution
