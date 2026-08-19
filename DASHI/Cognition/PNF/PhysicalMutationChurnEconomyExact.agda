module DASHI.Cognition.PNF.PhysicalMutationChurnEconomyExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import DASHI.Cognition.PNF.ComplexityArithmetic using (_+ᶜ_; _≤ᶜ_)

------------------------------------------------------------------------
-- Physical mutation economy is not semantic authority.
--
-- A compiler may reach exactly the same semantic/current projection through
-- very different numbers of INSERT/UPDATE/DELETE transitions.  This module
-- keeps those dimensions separate and gives the exact obligation required
-- before replacing delete/rebuild with narrower delta maintenance.
------------------------------------------------------------------------

record MutationChurnReceipt : Set where
  constructor mutationChurnReceipt
  field
    insertedRows : Nat
    updatedRows : Nat
    deletedRows : Nat
    finalAuthoritativeRows : Nat

open MutationChurnReceipt public

totalMutations : MutationChurnReceipt → Nat
totalMutations receipt =
  insertedRows receipt +ᶜ (updatedRows receipt +ᶜ deletedRows receipt)

------------------------------------------------------------------------
-- Exact semantic parity boundary for a physical maintenance rewrite.
------------------------------------------------------------------------

record ExactCurrentProjectionMaintenance
  (Input Projection : Set)
  : Set₁ where
  field
    rebuild : Input → Projection
    deltaMaintain : Input → Projection
    finalProjectionExact : ∀ input →
      deltaMaintain input ≡ rebuild input

open ExactCurrentProjectionMaintenance public

deltaMaintenanceCannotChangeFinalProjection :
  ∀ {Input Projection : Set}
    (law : ExactCurrentProjectionMaintenance Input Projection)
    (input : Input) →
  deltaMaintain law input ≡ rebuild law input
deltaMaintenanceCannotChangeFinalProjection law input =
  finalProjectionExact law input

------------------------------------------------------------------------
-- A physical optimisation claim requires non-increasing mutation work.
-- Equality is allowed here because semantic legality and physical improvement
-- remain separate questions; strictness can be supplied by a stronger receipt.
------------------------------------------------------------------------

record MutationNonWorsening
  (before after : MutationChurnReceipt)
  : Set where
  field
    mutationCountNonWorse : totalMutations after ≤ᶜ totalMutations before

open MutationNonWorsening public

------------------------------------------------------------------------
-- Cold-build delete/rebuild is not automatically wrong.
--
-- This negative boundary prevents a raw DELETE count from authorising delta
-- maintenance.  The replacement is legal only through the exact final
-- projection theorem above.
------------------------------------------------------------------------

record DeleteRebuildPressure : Set where
  constructor deleteRebuildPressure
  field
    observedDeletes : Nat
    observedReinsertions : Nat

open DeleteRebuildPressure public

record ChurnOptimisationCandidate
  (Input Projection : Set)
  : Set₁ where
  field
    exactMaintenance : ExactCurrentProjectionMaintenance Input Projection
    before after : MutationChurnReceipt
    nonWorsening : MutationNonWorsening before after

open ChurnOptimisationCandidate public

------------------------------------------------------------------------
-- Zero-mutation identity witness for already-current state.
------------------------------------------------------------------------

zeroMutationReceipt : MutationChurnReceipt
zeroMutationReceipt = mutationChurnReceipt zero zero zero zero

totalZeroMutationReceiptIsZero : totalMutations zeroMutationReceipt ≡ zero
totalZeroMutationReceiptIsZero = refl
