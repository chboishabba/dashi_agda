module DASHI.Analysis.CollatzSyracuseResidualWordCertificateFrontierExact where

------------------------------------------------------------------------
-- RESIDUAL WORD-CERTIFICATE FRONTIER COMPILER
--
-- This is the exact intake for finite cylinder search / affine word surgery.
-- At each finite horizon, a producer may cover residual literal starts below a
-- frontier by returning:
--   * an actual literal parity word of length m <= horizon,
--   * a uniform affine descent certificate for that word,
--   * proof that the start is above the certificate threshold.
--
-- The generic word-certificate theorem then yields literal strict descent.
-- Universal stopping still requires a separately proved unbounded residual
-- frontier.  Finite search is therefore useful but cannot promote itself.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_<_; _≤_)
import Data.Product as Product
open Product using (Σ; _×_; _,_)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.Analysis.CollatzSyracuseSurvivorFrontierExact as Frontier
import DASHI.Analysis.CollatzSyracuseEarlyCylinderEliminationExact as Early
import DASHI.Analysis.CollatzSyracuseResidualSurvivorFrontierExact as Residual
import DASHI.Analysis.CollatzSyracuseUniformWordDescentCertificateExact as Cert
import DASHI.Analysis.CollatzSyracuseUniversalStoppingCompilerExact as Universal

WordCertificateWitness :
  Nat → Syracuse.PositiveNat → Set
WordCertificateWitness horizon x =
  Σ Nat (λ m →
    (m ≤ horizon)
    ×
    Σ (Binary.BinaryWord m) (λ word →
      Σ (Cert.UniformWordDescentCertificate word) (λ certificate →
        (Cert.minimumStart certificate ≤ Syracuse.toNat x)
        ×
        (Itinerary.parityWord m x ≡ word))))

record ResidualWordCertificateFrontierSource : Set₁ where
  field
    frontier : Nat → Nat

    belowFrontierResidualCertificate :
      (horizon : Nat) →
      (x : Syracuse.PositiveNat) →
      8 ≤ Syracuse.toNat x →
      1 < Syracuse.toNat x →
      Early.EarlyResidualPrefix x →
      Syracuse.toNat x < frontier horizon →
      WordCertificateWitness horizon x

    frontierUnboundedOnResidual :
      (x : Syracuse.PositiveNat) →
      8 ≤ Syracuse.toNat x →
      1 < Syracuse.toNat x →
      Early.EarlyResidualPrefix x →
      Σ Nat (λ horizon → Syracuse.toNat x < frontier horizon)

open ResidualWordCertificateFrontierSource public

asResidualSurvivorFrontierSource :
  ResidualWordCertificateFrontierSource →
  Residual.ResidualSurvivorFrontierSource
asResidualSurvivorFrontierSource source = record
  { Residual.frontier = frontier source
  ; Residual.belowFrontierResidualDescends = descendWithin
  ; Residual.frontierUnboundedOnResidual =
      frontierUnboundedOnResidual source
  }
  where
    descendWithin :
      (horizon : Nat) →
      (x : Syracuse.PositiveNat) →
      8 ≤ Syracuse.toNat x →
      1 < Syracuse.toNat x →
      Early.EarlyResidualPrefix x →
      Syracuse.toNat x < frontier source horizon →
      Frontier.StrictDescentWithin horizon x
    descendWithin horizon x lower nontrivial residual xBelow =
      let
        witness = belowFrontierResidualCertificate
          source horizon x lower nontrivial residual xBelow
        m = Product.proj₁ witness
        rest₁ = Product.proj₂ witness
        mBound = Product.proj₁ rest₁
        rest₂ = Product.proj₂ rest₁
        word = Product.proj₁ rest₂
        rest₃ = Product.proj₂ rest₂
        certificate = Product.proj₁ rest₃
        rest₄ = Product.proj₂ rest₃
        threshold = Product.proj₁ rest₄
        wordMatch = Product.proj₂ rest₄
        descent = Cert.uniformWordCertificateImpliesDescent
          word certificate x threshold wordMatch
      in
      m , (mBound , descent)

asLiteralStrictDescentSource :
  ResidualWordCertificateFrontierSource →
  Universal.LiteralStrictDescentSource
asLiteralStrictDescentSource source =
  Residual.asLiteralStrictDescentSource
    (asResidualSurvivorFrontierSource source)

universalStoppingFromResidualWordCertificateFrontier :
  ResidualWordCertificateFrontierSource →
  (x : Syracuse.PositiveNat) →
  Universal.ReachesOne x
universalStoppingFromResidualWordCertificateFrontier source =
  Residual.universalStoppingFromResidualFrontier
    (asResidualSurvivorFrontierSource source)

record ResidualWordCertificateFrontierBoundary : Set where
  constructor residualWordCertificateFrontierBoundary
  field
    actualParityWordMatchRequired : Nat
    exactAffineCertificateRequired : Nat
    finiteCertificateCoverageCompilerPaid : Nat
    residualFrontierCompilerReused : Nat
    finiteSearchMayProduceWitnesses : Nat
    affineWordSurgeryMayProduceWitnesses : Nat
    finiteCoverageCreatesUnboundedFrontier : Nat
    unboundedResidualFrontierStillRequired : Nat

canonicalResidualWordCertificateFrontierBoundary :
  ResidualWordCertificateFrontierBoundary
canonicalResidualWordCertificateFrontierBoundary =
  residualWordCertificateFrontierBoundary 1 1 1 1 1 1 0 1
