module DASHI.Cognition.PNF.WorkConservingPersistence where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.OrderedWorldParserLookahead

------------------------------------------------------------------------
-- Typed staging is execution-only.  Publication permission is indexed by the
-- authority state, and there is deliberately no constructor granting staged
-- rows permission to extend the ordered world.
------------------------------------------------------------------------

data PersistenceAuthority : Set where
  provisionalExecutionOnly : PersistenceAuthority
  closedDocumentAuthority : PersistenceAuthority

data PublicationPermission : PersistenceAuthority → Set where
  closedDocumentMayPublish :
    PublicationPermission closedDocumentAuthority

provisionalStageCannotPublish :
  PublicationPermission provisionalExecutionOnly → ⊥
provisionalStageCannotPublish ()

record ProvisionalDocumentStage (source : Document) : Set where
  constructor provisionalDocumentStage
  field
    stageAuthority : PersistenceAuthority
    stageIsExecutionOnly :
      stageAuthority ≡ provisionalExecutionOnly

open ProvisionalDocumentStage public

canonicalProvisionalStage : ∀ source → ProvisionalDocumentStage source
canonicalProvisionalStage source =
  provisionalDocumentStage provisionalExecutionOnly refl

record ClosedPersistenceMerge (prior : World) (source : Document) : Set where
  constructor closedPersistenceMerge
  field
    mergedWorldStep : WorldStep prior source
    mergeAuthority : PersistenceAuthority
    mergeHasClosedDocumentAuthority :
      mergeAuthority ≡ closedDocumentAuthority

open ClosedPersistenceMerge public

publishClosedPersistenceMerge :
  ∀ {prior source} →
  OrderedWorldFold prior →
  (merge : ClosedPersistenceMerge prior source) →
  OrderedWorldFold (nextWorld (mergedWorldStep merge))
publishClosedPersistenceMerge prefix merge =
  publishNext prefix (mergedWorldStep merge)

------------------------------------------------------------------------
-- Worker ownership is transferred to the active critical kernel.  Parser
-- lookahead and foreground share the budget before persistence; persistence
-- receives the whole budget after the parser lane is quiesced.
------------------------------------------------------------------------

data CriticalKernel : Set where
  parserAndSemanticKernel : CriticalKernel
  postgresPersistenceKernel : CriticalKernel

record KernelAllocation (kernel : CriticalKernel) : Set where
  constructor kernelAllocation
  field
    kernelTotalWorkers : Nat
    activeKernelWorkers : Nat
    reservedOtherWorkers : Nat
    kernelWithinGlobalBudget :
      (activeKernelWorkers +ᶜ reservedOtherWorkers)
        ≤ᶜ kernelTotalWorkers

open KernelAllocation public

canonicalLookaheadKernelAllocation :
  KernelAllocation parserAndSemanticKernel
canonicalLookaheadKernelAllocation =
  kernelAllocation
    fourWorkers
    twoWorkers
    twoWorkers
    (≤ᶜ-refl fourWorkers)

canonicalPersistenceKernelAllocation :
  KernelAllocation postgresPersistenceKernel
canonicalPersistenceKernelAllocation =
  kernelAllocation
    fourWorkers
    fourWorkers
    zero
    (≤ᶜ-refl fourWorkers)

persistenceReceivesWholeBudget :
  activeKernelWorkers canonicalPersistenceKernelAllocation
    ≡ kernelTotalWorkers canonicalPersistenceKernelAllocation
persistenceReceivesWholeBudget = refl

record WorkConservingTransfer : Set where
  constructor workConservingTransfer
  field
    beforePersistence : KernelAllocation parserAndSemanticKernel
    duringPersistence : KernelAllocation postgresPersistenceKernel
    parserLaneQuiescedDuringPersistence : Bool
    parserLaneResumesAfterPersistence : Bool

open WorkConservingTransfer public

canonicalWorkConservingTransfer : WorkConservingTransfer
canonicalWorkConservingTransfer =
  workConservingTransfer
    canonicalLookaheadKernelAllocation
    canonicalPersistenceKernelAllocation
    true
    true

------------------------------------------------------------------------
-- Physical rows are partitioned across typed COPY lanes, then a fixed family
-- plan merges them under one ordered document savepoint.  Row-driven authority
-- writes and concurrent semantic publication are excluded from the declared
-- runtime status.
------------------------------------------------------------------------

data PersistenceExecutionShape : Set where
  rowDrivenRoundTrips : PersistenceExecutionShape
  typedParallelStageThenSetMerge : PersistenceExecutionShape

data StatementBound : Set where
  fixedPerArtifactFamily : Nat → StatementBound

record WorkConservingPersistenceStatus : Set where
  constructor workConservingPersistenceStatus
  field
    executionShape : PersistenceExecutionShape
    authorityStatementBound : StatementBound
    typedStageContainsJSONAuthority : Bool
    provisionalStageCanPublish : Bool
    parallelCopyBackendsAvailable : Bool
    setBasedAuthorityMergeAvailable : Bool
    oneOrderedDocumentPublication : Bool
    activeKernelReceivesWholeBudget : Bool

open WorkConservingPersistenceStatus public

currentWorkConservingPersistenceStatus : WorkConservingPersistenceStatus
currentWorkConservingPersistenceStatus =
  workConservingPersistenceStatus
    typedParallelStageThenSetMerge
    (fixedPerArtifactFamily fourWorkers)
    false
    false
    true
    true
    true
    true

record WorkConservingPersistenceBoundary : Set where
  constructor workConservingPersistenceBoundary
  field
    stageHasNoJSONAuthority :
      typedStageContainsJSONAuthority currentWorkConservingPersistenceStatus
        ≡ false
    provisionalRowsCannotPublish :
      provisionalStageCanPublish currentWorkConservingPersistenceStatus
        ≡ false
    parallelCopyIsPhysicalOnly :
      parallelCopyBackendsAvailable currentWorkConservingPersistenceStatus
        ≡ true
    authorityMergeIsSetBased :
      setBasedAuthorityMergeAvailable currentWorkConservingPersistenceStatus
        ≡ true
    semanticPublicationRemainsSingular :
      oneOrderedDocumentPublication currentWorkConservingPersistenceStatus
        ≡ true
    criticalKernelOwnsBudget :
      activeKernelReceivesWholeBudget currentWorkConservingPersistenceStatus
        ≡ true

canonicalWorkConservingPersistenceBoundary :
  WorkConservingPersistenceBoundary
canonicalWorkConservingPersistenceBoundary =
  workConservingPersistenceBoundary refl refl refl refl refl refl
