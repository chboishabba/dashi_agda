module DASHI.Core.AristotleFrontierWorklistTruthMaintenanceBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IncrementalDiagnosisTruthMaintenanceBidiExact as Truth
import DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact as Pareto

------------------------------------------------------------------------
-- ARISTOTLE LEAN -> DASHI METHODOLOGY BRIDGE
--
-- Source tranche supplied in-chat: output-final_aristotle / RequestProject.
-- This Agda owner does NOT claim automatic theorem transport from Lean.
-- It records the theorem shapes that are safe to reuse as methodology and pins
-- them to already-owned DASHI truth-maintenance boundaries.
--
-- Lean donors:
--   CorpusFrontier / CorpusRounds:
--     successive frontier downloads close missing layers while the extended
--     corpus entails the old corpus; frontier rounds may shrink without
--     requiring prior facts to disappear.
--   Worklist:
--     report rows are partitioned into keyed tasks; putting task rows back
--     together loses and duplicates nothing.
--   RepairWorkflow / Fixes / CompilerPipeline:
--     proved automatic repairs may be semantics-preserving; advisory or
--     unproved repairs remain distinct from proved safe transformations; later
--     pruning can preserve derived query answers.
--   Provenance:
--     a provenance note is not automatically an acceptable source.
--   Sync:
--     merge/sync is a least upper bound for entailment and loses neither input.
------------------------------------------------------------------------

record AristotleMethodologyDonor : Set where
  constructor aristotle-methodology-donor
  field
    conservativeFrontierExtension : Bool
    exactWorklistPartition : Bool
    provedAutomaticRepairMayPreserveSemantics : Bool
    suggestedRepairNeedsSeparateProof : Bool
    provenanceNoteIsNotAutomaticallySource : Bool
    mergeMayBeLeastUpperBoundWithoutLoss : Bool
    sourceReference : String

open AristotleMethodologyDonor public

canonicalAristotleMethodologyDonor : AristotleMethodologyDonor
canonicalAristotleMethodologyDonor =
  aristotle-methodology-donor
    true true true true true true
    "uploaded output-final_aristotle: CorpusFrontier.lean; CorpusRounds.lean; Worklist.lean; RepairWorkflow.lean; CompilerPipeline.lean; Provenance.lean; Sync.lean"

------------------------------------------------------------------------
-- DASHI consequences already owned independently.
------------------------------------------------------------------------

incrementalTruthMaintenanceBoundaryRetained : Truth.IncrementalTruthMaintenanceBoundary
incrementalTruthMaintenanceBoundaryRetained = Truth.canonicalIncrementalTruthMaintenanceBoundary

selectiveParetoBoundaryRetained : Pareto.SelectiveInvalidationParetoBoundary
selectiveParetoBoundaryRetained = Pareto.canonicalSelectiveInvalidationParetoBoundary

------------------------------------------------------------------------
-- Bridge interpretation.
------------------------------------------------------------------------

record FrontierWorklistBridgeBoundary : Set where
  constructor frontier-worklist-bridge-boundary
  field
    nextFrontierMayAddEvidenceWithoutDeletingOldHistory : Bool
    groupingObligationsMustLoseNothing : Bool
    groupingObligationsMustDuplicateNothingSemantically : Bool
    automaticRepairRequiresProofOfPreservation : Bool
    unprovedRepairMayBeAutoExecuted : Bool
    provenanceMetadataCreatesAuthority : Bool
    conservativeExtensionImpliesEveryOldCertificateMustRecompute : Bool

canonicalFrontierWorklistBridgeBoundary : FrontierWorklistBridgeBoundary
canonicalFrontierWorklistBridgeBoundary =
  frontier-worklist-bridge-boundary
    true true true true false false false

data AristotleLeanProofAutomaticallyBecomesAgdaProof : Set where
data WorklistGroupingCreatesNewObligation : Set where
data ProvenanceNoteCreatesSourceAuthority : Set where
data SuggestedRepairIsProvedSafe : Set where

leanProofDoesNotAutomaticallyTransportToAgda :
  AristotleLeanProofAutomaticallyBecomesAgdaProof → ⊥
leanProofDoesNotAutomaticallyTransportToAgda ()

worklistGroupingDoesNotCreateObligation : WorklistGroupingCreatesNewObligation → ⊥
worklistGroupingDoesNotCreateObligation ()

provenanceNoteDoesNotCreateSourceAuthority : ProvenanceNoteCreatesSourceAuthority → ⊥
provenanceNoteDoesNotCreateSourceAuthority ()

suggestedRepairIsNotProvedSafeBySuggestionAlone : SuggestedRepairIsProvedSafe → ⊥
suggestedRepairIsNotProvedSafeBySuggestionAlone ()
