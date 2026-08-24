{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.IndependentFibreBatchExecutionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- PARALLELISM IS LICENSED BY SEMANTIC INDEPENDENCE / COMMUTATION
--
-- Conversation/document fibres and independent sentence/block fibres are good
-- parallel units only when their state transitions commute on the shared
-- authority carrier.  Thread count, SQL statement count, or apparent physical
-- separability do not themselves establish this.
------------------------------------------------------------------------

record CommutingFibreUpdates (Fibre State : Set) : Set₁ where
  field
    Independent : Fibre → Fibre → Set
    update : Fibre → State → State

    independentUpdatesCommute :
      (left right : Fibre) →
      Independent left right →
      (state : State) →
      update left (update right state)
        ≡ update right (update left state)

open CommutingFibreUpdates public

independentExecutionOrderIsIrrelevant :
  ∀ {Fibre State : Set}
    (system : CommutingFibreUpdates Fibre State)
    (left right : Fibre) →
    Independent system left right →
    (state : State) →
  update system left (update system right state)
    ≡ update system right (update system left state)
independentExecutionOrderIsIrrelevant system =
  independentUpdatesCommute system

------------------------------------------------------------------------
-- A parallel/batched physical realization must still prove extensional equality
-- with the declared sequential semantic fold.  This is the bridge from local
-- commutation proofs to a concrete scheduler implementation.
------------------------------------------------------------------------

record ExactBatchRealization (Input Authority Receipt : Set) : Set₁ where
  field
    sequentialAuthority : Input → Authority
    batchedAuthority : Input → Authority
    batchExact : (input : Input) → batchedAuthority input ≡ sequentialAuthority input
    receipt : Input → Receipt

open ExactBatchRealization public

batchingPreservesAuthority :
  ∀ {Input Authority Receipt : Set}
    (batch : ExactBatchRealization Input Authority Receipt)
    (input : Input) →
  batchedAuthority batch input ≡ sequentialAuthority batch input
batchingPreservesAuthority batch = batchExact batch

------------------------------------------------------------------------
-- Anti-confusion boundary.
------------------------------------------------------------------------

data PhysicalConcurrencyImpliesIndependencePermission : Set where

data IndependentFibresRequireTinyTasksPermission : Set where

physicalConcurrencyDoesNotProveIndependence :
  PhysicalConcurrencyImpliesIndependencePermission → ⊥
physicalConcurrencyDoesNotProveIndependence ()

independenceDoesNotRequireTinyTaskGranularity :
  IndependentFibresRequireTinyTasksPermission → ⊥
independenceDoesNotRequireTinyTaskGranularity ()
