module DASHI.Cognition.PNF.StreamingPhysicalPartitionRefinementExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Physical parser-partition refinement gate.
--
-- StreamingSemanticPacmanKernelExact owns semantic prefix/suffix equality.
-- This module records what a finer/better-balanced parser schedule must preserve
-- before it may be used as a performance experiment.  Partition shape is
-- physical scheduling only; it never becomes a second semantic authority.
------------------------------------------------------------------------

record PartitionRefinementCertificate : Set₁ where
  constructor partitionRefinementCertificate
  field
    coarsePartitionCount : Nat
    refinedPartitionCount : Nat

    -- Exact disjoint ownership over canonical source coordinates is preserved.
    ExactOwnedCoverage : Set
    exactOwnedCoverage : ExactOwnedCoverage
    DisjointOwnedCoverage : Set
    disjointOwnedCoverage : DisjointOwnedCoverage

    -- Bilateral context may be duplicated physically, but it is evidence-only:
    -- it cannot create a second owned token/event or alter durable identity.
    ContextIsEvidenceOnly : Set
    contextIsEvidenceOnly : ContextIsEvidenceOnly

    -- Ordered parser observations presented to the semantic fold are preserved.
    -- A refinement may split/fuse physical work, but not reorder authority.
    OrderedObservationPreserved : Set
    orderedObservationPreserved : OrderedObservationPreserved

    -- The consumer-visible semantic authority is the same after finalization.
    SameSemanticAuthority : Set
    sameSemanticAuthority : SameSemanticAuthority

open PartitionRefinementCertificate public

------------------------------------------------------------------------
-- Performance evidence is empirical and must account for refinement cost.
------------------------------------------------------------------------

record PartitionRefinementPerformanceReceipt : Set where
  constructor partitionRefinementPerformanceReceipt
  field
    parserActiveWork : Nat
    semanticActiveWork : Nat
    parserSemanticOverlapWork : Nat
    duplicatedContextWork : Nat
    postParserTailWork : Nat
    endToEndWork : Nat

open PartitionRefinementPerformanceReceipt public

------------------------------------------------------------------------
-- Invalid inferences.
------------------------------------------------------------------------

data BetterBalanceImpliesSemanticEquivalence : Set where

data MorePartitionsImpliesBetterPerformance : Set where

data ContextDuplicationIsFree : Set where

data EOFCompletionAloneSelectsPartitionPolicy : Set where

balanceDoesNotProveSemantics : BetterBalanceImpliesSemanticEquivalence → ⊥
balanceDoesNotProveSemantics ()

morePartitionsDoNotProvePerformance : MorePartitionsImpliesBetterPerformance → ⊥
morePartitionsDoNotProvePerformance ()

contextDuplicationIsNotFree : ContextDuplicationIsFree → ⊥
contextDuplicationIsNotFree ()

eofCompletionAloneCannotSelectPolicy : EOFCompletionAloneSelectsPartitionPolicy → ⊥
eofCompletionAloneCannotSelectPolicy ()
