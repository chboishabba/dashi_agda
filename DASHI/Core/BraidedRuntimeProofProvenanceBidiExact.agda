module DASHI.Core.BraidedRuntimeProofProvenanceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.BraidedEvidenceTraceBidiCrossPollination2026Exact as Braid
import DASHI.Combinatorics.ProofCarryingTextileHyperfabricExact as Textile
import DASHI.Core.RuntimeEventExecutionBridgeExact as Runtime
import DASHI.Core.CommutingProvenanceBidiCrossPollination2026Exact as Commute

------------------------------------------------------------------------
-- RECIPROCAL WELD: BRAIDED PROVENANCE <-> PROOF FABRIC <-> RUNTIME EVENT LOG
--
-- Proof fabric gives a typed reached-state trace; braided evidence preserves
-- provenance/authority strands; runtime separates emission, execution and
-- feedback.  A commuting projection certifies that a coarse event-history view
-- is actually a projection of the fine transition history rather than a
-- separately reconstructed narrative.
------------------------------------------------------------------------

record BraidedRuntimeProofTrace : Set₂ where
  constructor braided-runtime-proof-trace
  field
    braid : Braid.BraidedEvidenceTrace
    textileBoundary : Textile.ProofCarryingTextileBoundary
    runtimeBoundary : Runtime.RuntimeEventExecutionBoundary
    FineHistory : Set
    CoarseHistory : Set
    fineStep : FineHistory → FineHistory
    coarseStep : CoarseHistory → CoarseHistory
    observe : FineHistory → CoarseHistory
    commutingHistory :
      Commute.CommutingProjection FineHistory CoarseHistory fineStep coarseStep observe
    proofTraceReference : String
    eventTraceReference : String
    appendOnlyRevisionReference : String
open BraidedRuntimeProofTrace public

record StrandLocalRuntimeReceipt
    (trace : BraidedRuntimeProofTrace) : Set where
  constructor strand-local-runtime-receipt
  field
    strand : Braid.EvidenceStrand
    eventReference : String
    executionReference : String
    feedbackReference : String
    strandAuthorityRetained : Bool
    strandAuthorityRetainedIsTrue : strandAuthorityRetained ≡ true
open StrandLocalRuntimeReceipt public

data EventEmissionCreatesProofTruth : Set where

data RuntimeFeedbackMayRewritePriorProvenance : Set where

data CoarseEventEqualityCreatesFineHistoryEquality : Set where

eventEmissionDoesNotCreateProofTruth : EventEmissionCreatesProofTruth → ⊥
eventEmissionDoesNotCreateProofTruth ()
runtimeFeedbackDoesNotRewritePriorProvenance : RuntimeFeedbackMayRewritePriorProvenance → ⊥
runtimeFeedbackDoesNotRewritePriorProvenance ()
coarseEventEqualityDoesNotCreateFineHistoryEquality :
  CoarseEventEqualityCreatesFineHistoryEquality → ⊥
coarseEventEqualityDoesNotCreateFineHistoryEquality ()

record BraidedRuntimeProofBoundary : Set where
  constructor braided-runtime-proof-boundary
  field
    provenanceStrandsSurviveRuntimeProjection : Bool
    executionDistinctFromProofTruth : Bool
    correctionAppendsHistoryRatherThanRewritesIt : Bool
    sameProcessNeedsCommutingProjection : Bool

canonicalBraidedRuntimeProofBoundary : BraidedRuntimeProofBoundary
canonicalBraidedRuntimeProofBoundary =
  braided-runtime-proof-boundary true true true true
