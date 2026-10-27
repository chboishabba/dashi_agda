module DASHI.Analysis.CollatzSyracuseResidualFrontierStrictnessGuardExact where

------------------------------------------------------------------------
-- RESIDUAL-FRONTIER STRICTNESS GUARD
--
-- A residual frontier is only useful if it genuinely escapes every residual
-- start.  This module makes the Hodge-style strictness condition explicit:
-- a globally bounded frontier cannot satisfy the required per-start
-- unboundedness once a residual start lies at or above that global bound.
--
-- Therefore a finite checked cutoff, however large, cannot be repackaged as
-- the terminal producer.  The theorem is on the same literal residual carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _<_)
import Data.Nat.Properties as NatP
import Data.Product as Product

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.Analysis.CollatzSyracuseEarlyCylinderEliminationExact as Early
import DASHI.Analysis.CollatzSyracuseResidualSurvivorFrontierExact as Residual
import DASHI.Analysis.CollatzSyracuseResidualWordCertificateFrontierExact as WordFrontier

record GloballyBoundedResidualFrontier
    (source : Residual.ResidualSurvivorFrontierSource) : Set where
  field
    bound : Nat
    frontierBound :
      (horizon : Nat) →
      Residual.frontier source horizon ≤ bound

open GloballyBoundedResidualFrontier public

globallyBoundedFrontierCannotCoverHighResidual :
  (source : Residual.ResidualSurvivorFrontierSource) →
  (bounded : GloballyBoundedResidualFrontier source) →
  (x : Syracuse.PositiveNat) →
  8 ≤ Syracuse.toNat x →
  1 < Syracuse.toNat x →
  Early.EarlyResidualPrefix x →
  bound bounded ≤ Syracuse.toNat x →
  ⊥
globallyBoundedFrontierCannotCoverHighResidual
    source bounded x lower nontrivial residual boundBelowX =
  let
    cover = Residual.frontierUnboundedOnResidual
      source x lower nontrivial residual
    horizon = Product.proj₁ cover
    xBelowFrontier = Product.proj₂ cover
    frontierBelowBound = frontierBound bounded horizon
    frontierBelowX = NatP.≤-trans frontierBelowBound boundBelowX
  in
  NatP.<⇒≱ xBelowFrontier frontierBelowX

record GloballyBoundedWordCertificateFrontier
    (source : WordFrontier.ResidualWordCertificateFrontierSource) : Set where
  field
    bound : Nat
    frontierBound :
      (horizon : Nat) →
      WordFrontier.frontier source horizon ≤ bound

open GloballyBoundedWordCertificateFrontier public

wordCertificateFrontierCannotBeGloballyBounded :
  (source : WordFrontier.ResidualWordCertificateFrontierSource) →
  (bounded : GloballyBoundedWordCertificateFrontier source) →
  (x : Syracuse.PositiveNat) →
  8 ≤ Syracuse.toNat x →
  1 < Syracuse.toNat x →
  Early.EarlyResidualPrefix x →
  GloballyBoundedWordCertificateFrontier.bound bounded ≤ Syracuse.toNat x →
  ⊥
wordCertificateFrontierCannotBeGloballyBounded
    source bounded x lower nontrivial residual boundBelowX =
  let
    residualSource = WordFrontier.asResidualSurvivorFrontierSource source
    residualBounded : GloballyBoundedResidualFrontier residualSource
    residualBounded = record
      { GloballyBoundedResidualFrontier.bound =
          GloballyBoundedWordCertificateFrontier.bound bounded
      ; GloballyBoundedResidualFrontier.frontierBound =
          GloballyBoundedWordCertificateFrontier.frontierBound bounded
      }
  in
  globallyBoundedFrontierCannotCoverHighResidual
    residualSource residualBounded x lower nontrivial residual boundBelowX

record ResidualFrontierStrictnessBoundary : Set where
  constructor residualFrontierStrictnessBoundary
  field
    literalResidualCarrierReused : Nat
    globallyBoundedFrontierRejected : Nat
    wordCertificateFrontierAlsoGuarded : Nat
    finiteCoverageCreatesUnboundedness : Nat
    largeFiniteVerificationCreatesUniversalStopping : Nat

canonicalResidualFrontierStrictnessBoundary :
  ResidualFrontierStrictnessBoundary
canonicalResidualFrontierStrictnessBoundary =
  residualFrontierStrictnessBoundary 1 1 1 0 0
