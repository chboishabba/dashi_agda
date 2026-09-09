{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact where

------------------------------------------------------------------------
-- LEAST-PRIVILEGE SEQUENTIAL CONVERGENCE
--
-- The historical `SequentialLimit` chooses a limit for every sequence and then
-- asserts every sequence converges to that choice.  The continuum extraction
-- route does not need that global structure.  It needs only a convergence
-- relation plus one theorem for the selected physical sequence (and extracted
-- subsequences when compactness is invoked).
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record SequentialConvergence (Object : Set) : Set₁ where
  field
    Converges : (Nat → Object) → Object → Set

open SequentialConvergence public

record SelectedSequenceLimit
    (Object : Set)
    (convergence : SequentialConvergence Object) : Set₁ where
  field
    sequence : Nat → Object
    target : Object
    selectedConverges : Converges convergence sequence target

open SelectedSequenceLimit public

selectedSequentialConvergenceCarrierLevel : ProofLevel
selectedSequentialConvergenceCarrierLevel = machineChecked
