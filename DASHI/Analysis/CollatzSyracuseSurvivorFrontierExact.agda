module DASHI.Analysis.CollatzSyracuseSurvivorFrontierExact where

------------------------------------------------------------------------
-- SURVIVOR-FRONTIER COMPILER FOR THE TERMINAL COLLATZ SOURCE
--
-- Density decay is not enough to eliminate a fixed exceptional integer.  The
-- stronger finite object needed for that promotion is a pointwise frontier:
-- by horizon m, every nontrivial start below frontier(m) has already attained
-- a value strictly below itself.  If those frontiers are unbounded, every
-- fixed positive integer is eventually covered and the literal strict-descent
-- source follows.
--
-- This module is deliberately agnostic about how the frontier is produced.
-- Exact affine-cylinder search, an external verified finite range, or a future
-- arithmetic ranking theorem may all feed the same source.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_<_; _≤_)
import Data.Product as Product
open Product using (Σ; _×_; _,_)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.Analysis.CollatzSyracuseUniversalStoppingCompilerExact as Stop

StrictDescentWithin :
  Nat → Syracuse.PositiveNat → Set
StrictDescentWithin horizon x =
  Σ Nat (λ m →
    (m ≤ horizon)
    ×
    (Syracuse.toNat (Syracuse.syracuseIterate m x)
      < Syracuse.toNat x))

record SurvivorFrontierSource : Set₁ where
  field
    frontier : Nat → Nat

    belowFrontierDescends :
      (horizon : Nat) →
      (x : Syracuse.PositiveNat) →
      1 < Syracuse.toNat x →
      Syracuse.toNat x < frontier horizon →
      StrictDescentWithin horizon x

    frontierUnbounded :
      (x : Syracuse.PositiveNat) →
      Σ Nat (λ horizon → Syracuse.toNat x < frontier horizon)

open SurvivorFrontierSource public

asLiteralStrictDescentSource :
  SurvivorFrontierSource →
  Stop.LiteralStrictDescentSource
asLiteralStrictDescentSource source = record
  { descend = λ x nontrivial →
      let
        cover = frontierUnbounded source x
        horizon = Product.proj₁ cover
        xBelow = Product.proj₂ cover
        witness = belowFrontierDescends source horizon x nontrivial xBelow
        m = Product.proj₁ witness
        boundedAndDescent = Product.proj₂ witness
      in
      m , Product.proj₂ boundedAndDescent
  }

universalStoppingFromUnboundedFrontier :
  SurvivorFrontierSource →
  (x : Syracuse.PositiveNat) →
  Stop.ReachesOne x
universalStoppingFromUnboundedFrontier source =
  Stop.universalStoppingFromStrictDescent
    (asLiteralStrictDescentSource source)

record SurvivorFrontierBoundary : Set where
  constructor survivorFrontierBoundary
  field
    finiteHorizonCoverageOwned : Nat
    unboundedFrontierWouldEliminateFixedExceptions : Nat
    densityDecayAloneConstructsFrontier : Nat
    exactAffineSearchMayFeedFrontier : Nat
    universalFrontierProducerOwned : Nat

canonicalSurvivorFrontierBoundary : SurvivorFrontierBoundary
canonicalSurvivorFrontierBoundary =
  survivorFrontierBoundary 1 1 0 1 0
