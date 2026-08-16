module DASHI.Crypto.MLKEMButterflyUncertaintyWorkFrontierExact where

------------------------------------------------------------------------
-- ML-KEM: BUTTERFLY STAGES ON THE SHARP 128 UNCERTAINTY FRONTIER
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Finite-field uncertainty source:
-- Martino Borello; Patrick Sole,
-- "The uncertainty principle over finite fields",
-- Discrete Mathematics 345 (2022), 112670.
-- DOI: 10.1016/j.disc.2021.112670.
--
-- PURPOSE
--
-- The existing butterfly theorem records the canonical FIPS widths
--
--   1,2,4,8,16,32,64,128
--
-- and complementary remaining same-parity fanouts
--
--   128,64,32,16,8,4,2,1.
--
-- Their product is exactly 128 at every stage.  Separately, the uncertainty
-- -> transition bridge says that a full-rank primitive move with source radius
-- r and verifier work w obeys
--
--   128 <= r*w.
--
-- This module puts those statements on the same theorem surface.  The result
-- is intentionally product-level: it does NOT identify runtime work with the
-- structural remaining fanout, nor does it claim every representation is one
-- of the eight canonical butterfly stages.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Crypto.MLKEMButterflyStageLocalityInvariantExact as Butterfly

harmonicFrontierArea : Butterfly.ButterflyStage → Nat
harmonicFrontierArea stage =
  Butterfly.sourceSupportWidth stage * Butterfly.remainingScalarFanout stage

harmonicFrontierAreaIs128 :
  (stage : Butterfly.ButterflyStage) →
  harmonicFrontierArea stage ≡ 128
harmonicFrontierAreaIs128 Butterfly.sourceStage = refl
harmonicFrontierAreaIs128 Butterfly.stage1 = refl
harmonicFrontierAreaIs128 Butterfly.stage2 = refl
harmonicFrontierAreaIs128 Butterfly.stage3 = refl
harmonicFrontierAreaIs128 Butterfly.stage4 = refl
harmonicFrontierAreaIs128 Butterfly.stage5 = refl
harmonicFrontierAreaIs128 Butterfly.stage6 = refl
harmonicFrontierAreaIs128 Butterfly.finalNTTStage = refl

------------------------------------------------------------------------
-- Full-rank stage-radius search primitive.
------------------------------------------------------------------------

record FullRankStageMove : Set where
  constructor full-rank-stage-move
  field
    stage : Butterfly.ButterflyStage
    changedSupport : Nat
    verifierWork : Nat

    withinCanonicalStageRadius :
      changedSupport ≤ Butterfly.sourceSupportWidth stage

    fullRankUncertaintyWork128 :
      128 ≤ changedSupport * verifierWork

open FullRankStageMove public

canonicalStageWorkProductLowerBound :
  (move : FullRankStageMove) →
  128 ≤ Butterfly.sourceSupportWidth (stage move) * verifierWork move
canonicalStageWorkProductLowerBound move =
  NatP.≤-trans
    (fullRankUncertaintyWork128 move)
    (NatP.*-monoˡ-≤
      (verifierWork move)
      (withinCanonicalStageRadius move))

record StageFrontierComparison (move : FullRankStageMove) : Set where
  constructor stage-frontier-comparison
  field
    structuralHarmonicProduct :
      harmonicFrontierArea (stage move) ≡ 128

    implementationWorkProductAtLeast128 :
      128 ≤ Butterfly.sourceSupportWidth (stage move) * verifierWork move

open StageFrontierComparison public

compareMoveToSharpHarmonicFrontier :
  (move : FullRankStageMove) → StageFrontierComparison move
compareMoveToSharpHarmonicFrontier move =
  stage-frontier-comparison
    (harmonicFrontierAreaIs128 (stage move))
    (canonicalStageWorkProductLowerBound move)

------------------------------------------------------------------------
-- Singular-budget version.
------------------------------------------------------------------------

record SingularBudgetStageMove : Set where
  constructor singular-budget-stage-move
  field
    stage : Butterfly.ButterflyStage
    changedSupport : Nat
    verifierWork : Nat
    singularBudget : Nat

    withinCanonicalStageRadius :
      changedSupport ≤ Butterfly.sourceSupportWidth stage

    uncertaintyWorkWithDefect128 :
      128 ≤ changedSupport * (verifierWork + singularBudget)

open SingularBudgetStageMove public

canonicalStageWorkDefectProductLowerBound :
  (move : SingularBudgetStageMove) →
  128 ≤
    Butterfly.sourceSupportWidth (stage move) *
    (verifierWork move + singularBudget move)
canonicalStageWorkDefectProductLowerBound move =
  NatP.≤-trans
    (uncertaintyWorkWithDefect128 move)
    (NatP.*-monoˡ-≤
      (verifierWork move + singularBudget move)
      (withinCanonicalStageRadius move))

------------------------------------------------------------------------
-- INTERPRETATION BOUNDARY
--
-- The equality
--
--   sourceSupportWidth(stage) * remainingScalarFanout(stage) = 128
--
-- shows that the eight canonical radix-2 stages lie on the same sharp product
-- frontier as the finite-field support uncertainty constant.  It is consistent
-- with viewing the butterfly filtration as a sequence of subgroup/annihilator
-- scales.  This module does not prove an equality characterization of all
-- uncertainty extremizers, nor does it identify remainingScalarFanout with
-- machine runtime.  Runtime still needs a concrete cost-domination producer.
------------------------------------------------------------------------
