module DASHI.Core.FiniteUniformBranchingHittingTailExact where

------------------------------------------------------------------------
-- GENERIC FINITE UNIFORM-BRANCHING HITTING-TAIL CORE
--
-- Cross-pollinated out of the non-Archimedean stopping-time lane.
--
-- This file deliberately knows nothing about Collatz, ZMod, Fourier analysis,
-- or spectral gaps.  A consumer supplies, for every surviving state, the full
-- finite list of block outcomes together with:
--
--   * exact branch count B;
--   * at least one killed continuation.
--
-- Then the number of surviving continuations is at most B-1.  Combined with
-- the already-owned generic block recurrence, this is the finite combinatorial
-- engine behind geometric hitting tails for any uniformly branching finite
-- process.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; _-_)
open import Data.List.Base using (length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Core.FiniteBooleanSurvivorCountExact as Survivor
import DASHI.Core.FiniteBlockSurvivalCountDecayExact as Decay

record UniformKilledBlockFamily : Set₁ where
  field
    State : Set
    branchFactor : Nat
    outcomes : State → List Bool
    exactBranchCount :
      (state : State) → length (outcomes state) ≡ branchFactor
    killedContinuation :
      (state : State) → false ∈ outcomes state

open UniformKilledBlockFamily public

oneBlockSurvivorsLeBranchMinusOne :
  (family : UniformKilledBlockFamily) →
  (state : State family) →
  Survivor.survivorCount (outcomes family state)
  ≤ branchFactor family - 1
oneBlockSurvivorsLeBranchMinusOne family state =
  let
    local :
      Survivor.survivorCount (outcomes family state)
      ≤ length (outcomes family state) - 1
    local = Survivor.falseMemberForcesAtMostLengthMinusOne
      (killedContinuation family state)
  in
  subst
    (λ total → Survivor.survivorCount (outcomes family state) ≤ total - 1)
    (exactBranchCount family state)
    local

------------------------------------------------------------------------
-- Process-level aggregation remains an explicit weld.
--
-- Per-state loss <= B-1 does not by itself define how a collection of current
-- survivors is aggregated into the next block.  Once a consumer supplies that
-- recurrence, the generic geometric theorem in FiniteBlockSurvivalCountDecay
-- applies with no source-specific mathematics.
------------------------------------------------------------------------

record UniformBranchingTailCompiler : Set₁ where
  field
    family : UniformKilledBlockFamily
    survivors : Nat → Nat
    aggregateOneBlockBound :
      (q : Nat) →
      survivors (Agda.Builtin.Nat.suc q)
      ≤ (branchFactor family - 1) * survivors q

open UniformBranchingTailCompiler public

asBlockSurvivalRecurrence :
  (compiler : UniformBranchingTailCompiler) →
  Decay.BlockSurvivalRecurrence
asBlockSurvivalRecurrence compiler = record
  { survivors = survivors compiler
  ; branchFactor = branchFactor (family compiler)
  ; contractionCount = branchFactor (family compiler) - 1
  ; contractionIsBranchFactorMinusOne = refl
  ; oneBlockBound = aggregateOneBlockBound compiler
  }

genericGeometricSurvivorBound :
  (compiler : UniformBranchingTailCompiler) →
  (q : Nat) →
  survivors compiler q
  ≤ Decay.powNat (branchFactor (family compiler) - 1) q
      * survivors compiler Agda.Builtin.Nat.zero
genericGeometricSurvivorBound compiler q =
  Decay.survivorCountGeometricBound
    (asBlockSurvivalRecurrence compiler) q

record GenericTailBoundary : Set where
  constructor genericTailBoundary
  field
    spectralGapRequired : Bool
    normalityRequired : Bool
    sourceSpecificCarrierRequired : Bool
    oneKilledContinuationPerStateRequired : Bool
    aggregateRecurrenceRequired : Bool
    geometricCountTailGeneric : Bool

canonicalGenericTailBoundary : GenericTailBoundary
canonicalGenericTailBoundary =
  genericTailBoundary false false false true true true

genericTailIsNotSpectral :
  GenericTailBoundary.spectralGapRequired canonicalGenericTailBoundary
  ≡ false
genericTailIsNotSpectral = refl

genericTailCoreOwned :
  GenericTailBoundary.geometricCountTailGeneric canonicalGenericTailBoundary
  ≡ true
genericTailCoreOwned = refl
