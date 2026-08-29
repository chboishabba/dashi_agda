{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSharedMarkedHessianToFiniteInfluenceExact where

------------------------------------------------------------------------
-- BIDI B -> C SPATIAL FUSION
--
-- BACKWARD from Row C:
-- the finite-speed/Dyson lane only needs one nonnegative finite influence
-- majorant M whose one-row mass is bounded uniformly.  Higher powers are then
-- controlled by powers of that same row mass.
--
-- FORWARD from Row B:
-- the shared CMP116 differentiated Hessian mark already supplies the
-- cutoff/volume/scale-uniform exponentially weighted row budget
--
--                    weighted Hessian row <= C_H.
--
-- Therefore the physical bridge should not ask for a second spatial-decay
-- theorem.  It should ask only for the SAME generator entries to be decomposed
-- into the literal marked Hessian row, yielding
--
--                    sum_y M(x,y) <= C_H.
--
-- This module packages exactly that same-object comparison and constructs the
-- finite influence carrier consumed by the existing all-power compiler.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanFiniteInfluenceNonnegativePowersExact as Positive
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

record SharedMarkedFiniteInfluenceBridge
    (Scale Volume Root Site : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    sites : List Site

    -- Absolute/covariant derivative-generator majorant on the SAME finite
    -- Yang--Mills density whose Hessian is represented by `shared`.
    influence : Site → Site → ℚ
    influenceNonnegative : ∀ x y → 0ℚ ≤ influence x y

    -- This is the only physical spatial weld requested here.  It identifies the
    -- literal finite row with the already-owned weighted CMP116 Hessian budget.
    influenceRowBelowSharedHessian : ∀ x →
      Sums.sumRational sites (influence x)
      ≤ Shared.hessianAnalyticConstant shared

open SharedMarkedFiniteInfluenceBridge public

asFiniteInfluenceMajorant :
  ∀ {Scale Volume Root Site} →
  SharedMarkedFiniteInfluenceBridge Scale Volume Root Site →
  Power.NonnegativeFiniteInfluenceMajorant Site
asFiniteInfluenceMajorant dataSet = record
  { Power.NonnegativeFiniteInfluenceMajorant.sites = sites dataSet
  ; Power.NonnegativeFiniteInfluenceMajorant.majorant = influence dataSet
  ; Power.NonnegativeFiniteInfluenceMajorant.majorantNonnegative =
      influenceNonnegative dataSet
  ; Power.NonnegativeFiniteInfluenceMajorant.rowMass =
      Shared.hessianAnalyticConstant (shared dataSet)
  ; Power.NonnegativeFiniteInfluenceMajorant.rowMassNonnegative =
      Shared.markedConstantNonnegative
        (shared dataSet) Shared.hessianMark
  ; Power.NonnegativeFiniteInfluenceMajorant.rowMassBound =
      influenceRowBelowSharedHessian dataSet
  }

influencePowerRowMassBound :
  ∀ {Scale Volume Root Site}
    (dataSet : SharedMarkedFiniteInfluenceBridge Scale Volume Root Site) →
  ∀ n x →
  Sums.sumRational
    (Power.sites (asFiniteInfluenceMajorant dataSet))
    (Power.majorantPowerPositive (asFiniteInfluenceMajorant dataSet) n x)
  ≤ Power.rationalPower
      (Shared.hessianAnalyticConstant (shared dataSet)) (suc n)
influencePowerRowMassBound dataSet =
  Positive.positivePowerRowMassBoundFromMajorant
    (asFiniteInfluenceMajorant dataSet)

sharedMarkedHessianToFiniteInfluenceCarrierLevel : ProofLevel
sharedMarkedHessianToFiniteInfluenceCarrierLevel = machineChecked

sharedMarkedHessianToAllInfluencePowerRowsLevel : ProofLevel
sharedMarkedHessianToAllInfluencePowerRowsLevel = machineChecked

-- Highest-alpha physical Row-C spatial seam after the BIDI reduction:
-- identify the absolute covariant derivative generator of the SAME Heat/Doob
-- dynamics with a finite majorant whose literal row sum is bounded by the
-- already-required CMP116 hessian mark.  No independent all-power positivity,
-- all-power row estimate, or second spatial shell theorem is then needed.
literalSameDensityGeneratorRowBelowSharedHessianLevel : ProofLevel
literalSameDensityGeneratorRowBelowSharedHessianLevel = conditional
