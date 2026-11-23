module DASHI.Cognition.PNF.RelationDeltaReconciliationExact where

open import Agda.Builtin.Equality using (_≡_)
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
