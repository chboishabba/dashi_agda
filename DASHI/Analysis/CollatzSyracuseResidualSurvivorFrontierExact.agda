module DASHI.Analysis.CollatzSyracuseResidualSurvivorFrontierExact where

------------------------------------------------------------------------
-- SURVIVOR FRONTIER ON THE REFINED RESIDUAL PREFIX FAMILIES
--
-- The early literal eliminator leaves only 11011, 11101, and 1111... starts.
-- This module gives finite exact search / affine word surgery a theorem-bearing
-- intake restricted to that residual same-object carrier.  As elsewhere, finite
-- coverage does not become universal stopping unless the residual frontier is
-- proved unbounded on every residual start.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_<_; _≤_)
import Data.Product as Product
open Product using (Σ; _,_)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.Analysis.CollatzSyracuseSurvivorFrontierExact as Frontier
import DASHI.Analysis.CollatzSyracuseEarlyCylinderEliminationExact as Early
import DASHI.Analysis.CollatzSyracuseUniversalStoppingCompilerExact as Universal

record ResidualSurvivorFrontierSource : Set₁ where
  field
    frontier : Nat → Nat

    belowFrontierResidualDescends :
      (horizon : Nat) →
      (x : Syracuse.PositiveNat) →
      8 ≤ Syracuse.toNat x →
      1 < Syracuse.toNat x →
      Early.EarlyResidualPrefix x →
      Syracuse.toNat x < frontier horizon →
      Frontier.StrictDescentWithin horizon x

    frontierUnboundedOnResidual :
      (x : Syracuse.PositiveNat) →
      8 ≤ Syracuse.toNat x →
      1 < Syracuse.toNat x →
      Early.EarlyResidualPrefix x →
      Σ Nat (λ horizon → Syracuse.toNat x < frontier horizon)

open ResidualSurvivorFrontierSource public

asEarlyResidualTailSource :
  ResidualSurvivorFrontierSource →
  Early.EarlyResidualTailSource
asEarlyResidualTailSource source = record
  { Early.residualDescend = λ x lower nontrivial residual →
      let
        cover = frontierUnboundedOnResidual
          source x lower nontrivial residual
        horizon = Product.proj₁ cover
        xBelow = Product.proj₂ cover
        witness = belowFrontierResidualDescends
          source horizon x lower nontrivial residual xBelow
        k = Product.proj₁ witness
        boundedAndDescent = Product.proj₂ witness
      in
      k , Product.proj₂ boundedAndDescent
  }

asLiteralStrictDescentSource :
  ResidualSurvivorFrontierSource →
  Universal.LiteralStrictDescentSource
asLiteralStrictDescentSource source =
  Early.asLiteralStrictDescentSource
    (asEarlyResidualTailSource source)

universalStoppingFromResidualFrontier :
  ResidualSurvivorFrontierSource →
  (x : Syracuse.PositiveNat) →
  Universal.ReachesOne x
universalStoppingFromResidualFrontier source =
  Early.universalStoppingFromEarlyResidualTail
    (asEarlyResidualTailSource source)

record ResidualSurvivorFrontierBoundary : Set where
  constructor residualSurvivorFrontierBoundary
  field
    residualCarrierAlreadyRefined : Nat
    finiteResidualCoverageInterfacePaid : Nat
    residualFrontierCompilerPaid : Nat
    finiteSearchMayFeedResidualCoverage : Nat
    affineWordSurgeryMayFeedResidualCoverage : Nat
    densityCreatesUnboundedResidualFrontier : Nat
    unboundedResidualFrontierProducerPaid : Nat
    onlyUnboundedLeafIsResidualFrontierGrowth : Nat

canonicalResidualSurvivorFrontierBoundary : ResidualSurvivorFrontierBoundary
canonicalResidualSurvivorFrontierBoundary =
  residualSurvivorFrontierBoundary 1 1 1 1 1 0 0 1
