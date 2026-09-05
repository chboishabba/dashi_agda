module DASHI.Core.FiniteBlockSurvivalCountDecayExact where

------------------------------------------------------------------------
-- FINITE BLOCK SURVIVAL COUNT DECAY
--
-- Suppose a finite branching process is grouped into fixed blocks.  If each
-- surviving state has at most `branchFactor - 1` surviving continuations across
-- one block, then the survivor counts decay geometrically:
--
--   S(q+1) <= c S(q),  c = branchFactor - 1
--
-- implies
--
--   S(q) <= c^q S(0).
--
-- For binary Markov words of block length m, branchFactor = 2^m.  A designated
-- hitting word from every survivor gives c <= 2^m - 1 and therefore, after
-- normalization by the total 2^(mq) words, a probability envelope
--
--   (1 - 2^(-m))^q.
--
-- This theorem is purely finite combinatorics.  It does not use matrix
-- normality, eigenvalue interlacing or a spectral-radius estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _-_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP using
  (≤-refl; ≤-trans; *-mono-≤; *-assoc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

powNat : Nat → Nat → Nat
powNat base zero = 1
powNat base (suc exponent) = base * powNat base exponent

record BlockSurvivalRecurrence : Set where
  constructor blockSurvivalRecurrence
  field
    survivors : Nat → Nat
    branchFactor : Nat
    contractionCount : Nat
    contractionIsBranchFactorMinusOne :
      contractionCount ≡ branchFactor - 1
    oneBlockBound :
      (q : Nat) →
      survivors (suc q) ≤ contractionCount * survivors q

open BlockSurvivalRecurrence public

survivorCountGeometricBound :
  (data : BlockSurvivalRecurrence) →
  (q : Nat) →
  survivors data q
  ≤ powNat (contractionCount data) q * survivors data zero
survivorCountGeometricBound data zero =
  ≤-refl
survivorCountGeometricBound data (suc q) =
  let
    c = contractionCount data
    Sq = survivors data q
    S0 = survivors data zero

    step : survivors data (suc q) ≤ c * Sq
    step = oneBlockBound data q

    induction : Sq ≤ powNat c q * S0
    induction = survivorCountGeometricBound data q

    scaled : c * Sq ≤ c * (powNat c q * S0)
    scaled = *-mono-≤ ≤-refl induction

    reassociate :
      c * (powNat c q * S0)
      ≡ powNat c (suc q) * S0
    reassociate = sym (*-assoc c (powNat c q) S0)
  in
  ≤-trans step
    (subst
      (λ upper → c * Sq ≤ upper)
      reassociate
      scaled)

record BinaryHittingBlockBoundary : Set where
  constructor binaryHittingBlockBoundary
  field
    directedReachabilityProvidesFinitePath : Bool
    finiteStateSpaceProvidesUniformBlockLength : Bool
    oneDesignatedWordPerStateProvidesOneKilledContinuation : Bool
    oneKilledContinuationGivesBlockCountBound : Bool
    geometricCountIterationNowOwned : Bool
    matrixNormalityRequired : Bool

canonicalBinaryHittingBlockBoundary : BinaryHittingBlockBoundary
canonicalBinaryHittingBlockBoundary =
  binaryHittingBlockBoundary true true true false true false

countIterationOwned :
  BinaryHittingBlockBoundary.geometricCountIterationNowOwned
    canonicalBinaryHittingBlockBoundary
  ≡ true
countIterationOwned = refl

matrixSpectralRoutePruned :
  BinaryHittingBlockBoundary.matrixNormalityRequired
    canonicalBinaryHittingBlockBoundary
  ≡ false
matrixSpectralRoutePruned = refl

oneRemainingCombinatorialLeaf :
  BinaryHittingBlockBoundary.oneKilledContinuationGivesBlockCountBound
    canonicalBinaryHittingBlockBoundary
  ≡ false
oneRemainingCombinatorialLeaf = refl
