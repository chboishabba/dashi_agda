module DASHI.Core.StatefulSemanticBackendExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- FUTURE HOT-PATH BACKEND SHAPE
--
-- A native/Rust backend, if admitted by measurement, should be a long-lived
-- versioned workspace: initialize once, then consume changed/deleted source
-- observations relative to a parent state. Per-commit whole-corpus
-- serialization/subprocess startup is explicitly not the target architecture.
------------------------------------------------------------------------

data WorkspaceBackendOperation : Set where
  initializeWorkspace : WorkspaceBackendOperation
  forkParentState : WorkspaceBackendOperation
  applyChangedObservations : WorkspaceBackendOperation
  deleteSourceObservation : WorkspaceBackendOperation
  emitSemanticPatchReceipt : WorkspaceBackendOperation

record StatefulBackendBoundary : Set where
  constructor statefulBackendBoundary
  field
    rustBackendShouldSpawnPerCommit : Bool
    rustBackendShouldSpawnPerCommitIsFalse :
      rustBackendShouldSpawnPerCommit ≡ false

    rustBackendShouldReceiveWholeCorpusPerCommit : Bool
    rustBackendShouldReceiveWholeCorpusPerCommitIsFalse :
      rustBackendShouldReceiveWholeCorpusPerCommit ≡ false

    backendShouldRetainVersionedWorkspaceState : Bool
    backendShouldRetainVersionedWorkspaceStateIsTrue :
      backendShouldRetainVersionedWorkspaceState ≡ true

    pythonOrchestrationMayRemainOutsideNativeCore : Bool
    pythonOrchestrationMayRemainOutsideNativeCoreIsTrue :
      pythonOrchestrationMayRemainOutsideNativeCore ≡ true

canonicalStatefulBackendBoundary : StatefulBackendBoundary
canonicalStatefulBackendBoundary =
  statefulBackendBoundary
    false refl
    false refl
    true refl
    true refl
