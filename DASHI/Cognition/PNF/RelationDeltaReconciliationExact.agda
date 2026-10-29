module DASHI.Cognition.PNF.RelationDeltaReconciliationExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Desired/current keyed relation reconciliation.
--
-- A key owns semantic identity for one reducer.  Payload changes are distinct
-- from membership changes.  Unchanged keys are retained verbatim and do not
-- manufacture execution transitions merely because the reducer ran again.
------------------------------------------------------------------------

record RelationDeltaReceipt : Set where
  constructor relationDeltaReceipt
  field
    desiredRows : Nat
    currentRows : Nat
    addedRows : Nat
    removedRows : Nat
    replacedRows : Nat
    unchangedRowsSkipped : Nat
    physicalRowMutations : Nat

    desiredPartitionExact :
      desiredRows ≡ addedRows + replacedRows + unchangedRowsSkipped

    currentPartitionExact :
      currentRows ≡ removedRows + replacedRows + unchangedRowsSkipped

    physicalMutationExact :
      physicalRowMutations ≡
        addedRows + removedRows + (2 * replacedRows)

open RelationDeltaReceipt public

------------------------------------------------------------------------
-- Transition emission is change-sensitive, not evaluation-sensitive.
------------------------------------------------------------------------

record RelationDeltaTransitionBoundary : Set where
  constructor relationDeltaTransitionBoundary
  field
    reconciliation : RelationDeltaReceipt
    emittedTransitionRows : Nat
    emittedTransitionsExact :
      emittedTransitionRows ≡
        addedRows reconciliation
        + removedRows reconciliation
        + (2 * replacedRows reconciliation)

open RelationDeltaTransitionBoundary public

------------------------------------------------------------------------
-- Invalid runtime interpretations.
------------------------------------------------------------------------

data UnchangedRowRequiresRewrite : Set where

data ReducerInvocationIsSemanticChange : Set where

data PhysicalMutationCountIsAuthorityCount : Set where

data DesiredRelationMaySkipCurrentComparison : Set where

unchangedRowNeedNotRewrite : UnchangedRowRequiresRewrite → ⊥
unchangedRowNeedNotRewrite ()

runningReducerDoesNotManufactureChange : ReducerInvocationIsSemanticChange → ⊥
runningReducerDoesNotManufactureChange ()

physicalWritesAreNotSemanticAuthority : PhysicalMutationCountIsAuthorityCount → ⊥
physicalWritesAreNotSemanticAuthority ()

desiredMustCompareCurrent : DesiredRelationMaySkipCurrentComparison → ⊥
desiredMustCompareCurrent ()


------------------------------------------------------------------------
-- Durable runtime certification.
--
-- A transaction-local reconciliation observation is not a surviving runtime
-- receipt.  Runtime certification requires a persisted receipt after commit.
-- This keeps rollback evidence separate from durable execution evidence.
------------------------------------------------------------------------

record PersistedRelationDeltaReceipt : Set where
  constructor persistedRelationDeltaReceipt
  field
    persistedReconciliation : RelationDeltaReceipt
    persisted : Bool
    persistedIsTrue : persisted ≡ true

open PersistedRelationDeltaReceipt public

data RolledBackReconciliationReceiptSurvives : Set where

rolledBackReconciliationCannotCertify :
  RolledBackReconciliationReceiptSurvives → ⊥
rolledBackReconciliationCannotCertify ()

------------------------------------------------------------------------
-- Fixed-point replay witness.
--
-- When desired and current rows are identical, reconciliation still examines
-- the logical relation but emits no physical mutation.  This is the exact
-- second-replay certificate required by the active SensibLaw reducer.
------------------------------------------------------------------------

noOpRelationDeltaReceipt : Nat → RelationDeltaReceipt
noOpRelationDeltaReceipt rows =
  relationDeltaReceipt
    rows
    rows
    0
    0
    0
    rows
    0
    refl
    refl
    refl

persistedNoOpRelationDeltaReceipt :
  Nat → PersistedRelationDeltaReceipt
persistedNoOpRelationDeltaReceipt rows =
  persistedRelationDeltaReceipt
    (noOpRelationDeltaReceipt rows)
    true
    refl

persistedNoOpPhysicalMutationsAreZero :
  ∀ rows →
  physicalRowMutations
    (persistedReconciliation
      (persistedNoOpRelationDeltaReceipt rows))
  ≡ 0
persistedNoOpPhysicalMutationsAreZero rows = refl

persistedNoOpDesiredPartitionExact :
  ∀ rows →
  desiredRows
    (persistedReconciliation
      (persistedNoOpRelationDeltaReceipt rows))
  ≡
  addedRows
    (persistedReconciliation
      (persistedNoOpRelationDeltaReceipt rows))
  +
  replacedRows
    (persistedReconciliation
      (persistedNoOpRelationDeltaReceipt rows))
  +
  unchangedRowsSkipped
    (persistedReconciliation
      (persistedNoOpRelationDeltaReceipt rows))
persistedNoOpDesiredPartitionExact rows =
  desiredPartitionExact
    (persistedReconciliation
      (persistedNoOpRelationDeltaReceipt rows))
