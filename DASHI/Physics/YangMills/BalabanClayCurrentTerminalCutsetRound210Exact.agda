{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound210Exact where

------------------------------------------------------------------------
-- ROUND210: SELECTED-CONVERGENCE CANONICAL FRONTIER
--
-- The historical SequentialLimit carrier asserted convergence of every sequence
-- to a chosen total limit.  The preferred route no longer depends on it.
--
-- Canonical convergence chain:
--
--   selected typed moments
--     + global moment compact containment
--   -> uniform tightness
--   -> every literal subsequence tight
--   -> selected Prokhorov extraction
--   -> determining-test cluster uniqueness
--   -> compact+unique full selected-sequence convergence.
--
-- T2/T3/T4 all share the selected weak-expectation topology/test-class meaning.
-- The old total-limit carrier and its generic closure fields remain compatibility
-- surfaces only.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound209Exact as R209
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Selected
import DASHI.Physics.YangMills.BalabanClayT5SelectedMomentCompactContainmentExact as Moment
import DASHI.Physics.YangMills.BalabanClayT5SelectedUniformTightnessBridgeExact as Uniform
import DASHI.Physics.YangMills.BalabanClayT5SelectedProkhorovExtractionExact as Prokhorov
import DASHI.Physics.YangMills.BalabanClayT5SelectedCompactUniqueFullSequenceExact as CompactUnique
import DASHI.Physics.YangMills.BalabanClayT5SelectedWeakExpectationClosureExact as Weak
import DASHI.Physics.YangMills.BalabanClayT5SelectedWeakGramReflectionClosureExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5SelectedContinuumOSExact as OS
import DASHI.Physics.YangMills.BalabanClayT5SelectedContinuumOSGapBridgeExact as Gap
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf210 : Set where
  -- Genuine T1 wall: existing selected moment theorem must control escape from
  -- one admissible compact witness uniformly in cutoff.
  physicalGlobalMomentCompactContainment : T5PreferredContinuumLeaf210

  -- Shared T2/T3/T4 representation/topology seam.
  physicalSelectedWeakExpectationTopologyAndCompleteTestClassMeaning :
    T5PreferredContinuumLeaf210

  -- Remaining selected continuum Schwinger properties/semantics.
  physicalContinuumEuclideanCovariance : T5PreferredContinuumLeaf210
  physicalContinuumSymmetry : T5PreferredContinuumLeaf210
  physicalContinuumTemperedness : T5PreferredContinuumLeaf210
  physicalContinuumRegularity : T5PreferredContinuumLeaf210
  physicalContinuumClustering : T5PreferredContinuumLeaf210
  physicalGramReflectionToSchwingerReflectionMeaning : T5PreferredContinuumLeaf210

preferredT5ContinuumCut210 : List T5PreferredContinuumLeaf210
preferredT5ContinuumCut210 =
  physicalGlobalMomentCompactContainment ∷
  physicalSelectedWeakExpectationTopologyAndCompleteTestClassMeaning ∷
  physicalContinuumEuclideanCovariance ∷
  physicalContinuumSymmetry ∷
  physicalContinuumTemperedness ∷
  physicalContinuumRegularity ∷
  physicalContinuumClustering ∷
  physicalGramReflectionToSchwingerReflectionMeaning ∷ []

selectedConvergenceCarrierLevel : ProofLevel
selectedConvergenceCarrierLevel = Selected.selectedSequentialConvergenceCarrierLevel

selectedMomentCompactContainmentCompilerLevel : ProofLevel
selectedMomentCompactContainmentCompilerLevel =
  Moment.selectedMomentCompactContainmentCompilerLevel

selectedUniformTightnessBridgeLevel : ProofLevel
selectedUniformTightnessBridgeLevel = Uniform.selectedUniformTightnessBridgeLevel

selectedProkhorovExtractionCompilerLevel : ProofLevel
selectedProkhorovExtractionCompilerLevel =
  Prokhorov.selectedProkhorovExtractionCompilerLevel

selectedCompactUniqueCompilerLevel : ProofLevel
selectedCompactUniqueCompilerLevel = CompactUnique.selectedCompactUniqueCompilerLevel

selectedWeakExpectationPropertyClosureLevel : ProofLevel
selectedWeakExpectationPropertyClosureLevel =
  Weak.selectedWeakExpectationPropertyClosureLevel

selectedWeakTopologyClusterAgreementLevel : ProofLevel
selectedWeakTopologyClusterAgreementLevel =
  Weak.selectedWeakTopologyClusterAgreementLevel

selectedWeakGramReflectionClosureLevel : ProofLevel
selectedWeakGramReflectionClosureLevel =
  Gram.selectedWeakGramReflectionClosureLevel

selectedContinuumOSCarrierLevel : ProofLevel
selectedContinuumOSCarrierLevel = OS.selectedContinuumOSCarrierLevel

selectedContinuumOSGapCompilerLevel : ProofLevel
selectedContinuumOSGapCompilerLevel = Gap.selectedContinuumOSGapCompilerLevel

data T1PrerequisiteStatus210 : Set where
  missingGlobalMomentCompactContainment : T1PrerequisiteStatus210
  readyForSelectedUniformTightness : T1PrerequisiteStatus210

preferredCurrentT1Status210 : T1PrerequisiteStatus210
preferredCurrentT1Status210 = missingGlobalMomentCompactContainment

data T234PrerequisiteStatus210 : Set where
  missingSelectedWeakExpectationTopologyAndCompleteTestClassMeaning :
    T234PrerequisiteStatus210
  readyForSelectedClusterPropertyAndGramCompilers : T234PrerequisiteStatus210

preferredCurrentT234Status210 : T234PrerequisiteStatus210
preferredCurrentT234Status210 =
  missingSelectedWeakExpectationTopologyAndCompleteTestClassMeaning

-- Round209 remains a compatibility audit of the old closure carrier.  The
-- preferred path no longer needs its total SequentialLimit structure.
round209CompatibilityAuditRetained : ProofLevel
round209CompatibilityAuditRetained = R209.currentYMTerminalCutsetRound209Level

legacyTotalSequentialLimitNotRequiredByPreferredRoute : Bool
legacyTotalSequentialLimitNotRequiredByPreferredRoute = true

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound210Level : ProofLevel
currentYMTerminalCutsetRound210Level = machineChecked

literalPreferredT5ContinuumLeaf210Level : ProofLevel
literalPreferredT5ContinuumLeaf210Level = conditional
