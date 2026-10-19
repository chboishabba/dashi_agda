module DASHI.Analysis.CollatzSyracuseUniformHittingBlockExact where

------------------------------------------------------------------------
-- FINITE-LEVEL HITTING BLOCK BOUNDARY
--
-- This module never promotes a finite residue-level reachability statement to
-- all positive integers.  The finite target, level, and reachability producer
-- remain explicit fields.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

record SyracuseFiniteHittingSource : Set₁ where
  field
    level : Nat
    State : Set
    target : State
    blockLength : Nat
    chosenHitWithinBlock : State → Set

open SyracuseFiniteHittingSource public

record FiniteHittingBoundary : Set where
  constructor finiteHittingBoundary
  field
    finiteLevelExplicit : Nat
    targetExplicit : Nat
    finiteReachabilityPromotesToAllIntegers : Nat

canonicalFiniteHittingBoundary : FiniteHittingBoundary
canonicalFiniteHittingBoundary = finiteHittingBoundary 1 1 0
