{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSharedMarkedHessianToWeightedInfluenceExact where

------------------------------------------------------------------------
-- BIDI B -> C SPATIAL ADAPTER WITH THE EXPONENTIAL WEIGHT RETAINED
--
-- The weaker Round97 adapter forgot the spatial weight after using CMP116 to
-- obtain C_H.  For the finite-speed consumer the stronger and more natural
-- object is the weighted row itself.
--
-- Backward target:
--   one submultiplicative weighted influence matrix whose powers preserve the
--   same weight.
--
-- Forward source:
--   `SharedMarkedAnalyticShellExact` +
--   `BalabanRootedKPToExponentialWeightedHessianExact` already give the physical
--   Hessian mark with a cutoff-uniform exponential weight and row constant C_H.
--
-- Hence the only source weld is equality/comparison between the SAME stochastic
-- derivative-generator entries and that marked Hessian row.  Once supplied,
-- `BalabanFiniteWeightedInfluencePowerExact` propagates the exponential weight
-- through every finite Dyson power.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact as Weighted
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

record SharedMarkedWeightedInfluenceBridge
    (Scale Volume Root Site : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    sites : List Site
    influence weight : Site → Site → ℚ

    influenceNonnegative : ∀ x y → 0ℚ ≤ influence x y
    weightNonnegative : ∀ x y → 0ℚ ≤ weight x y
    weightAtLeastOne : ∀ x y → 1ℚ ≤ weight x y
    weightTriangle : ∀ x middle y →
      weight x y ≤ weight x middle * weight middle y

    -- Literal same-object row comparison.  The RHS is not a new constant: it is
    -- exactly the CMP116 marked Hessian analytic constant already required by B.
    weightedGeneratorRowBelowSharedHessian : ∀ x →
      Sums.sumRational sites (λ y → weight x y * influence x y)
      ≤ Shared.hessianAnalyticConstant shared

open SharedMarkedWeightedInfluenceBridge public

asWeightedFiniteInfluence :
  ∀ {Scale Volume Root Site} →
  SharedMarkedWeightedInfluenceBridge Scale Volume Root Site →
  Weighted.WeightedFiniteInfluenceMajorant Site
asWeightedFiniteInfluence dataSet = record
  { Weighted.WeightedFiniteInfluenceMajorant.sites = sites dataSet
  ; Weighted.WeightedFiniteInfluenceMajorant.influence = influence dataSet
  ; Weighted.WeightedFiniteInfluenceMajorant.weight = weight dataSet
  ; Weighted.WeightedFiniteInfluenceMajorant.influenceNonnegative =
      influenceNonnegative dataSet
  ; Weighted.WeightedFiniteInfluenceMajorant.weightNonnegative =
      weightNonnegative dataSet
  ; Weighted.WeightedFiniteInfluenceMajorant.weightAtLeastOne =
      weightAtLeastOne dataSet
  ; Weighted.WeightedFiniteInfluenceMajorant.weightTriangle =
      weightTriangle dataSet
  ; Weighted.WeightedFiniteInfluenceMajorant.weightedRowMass =
      Shared.hessianAnalyticConstant (shared dataSet)
  ; Weighted.WeightedFiniteInfluenceMajorant.weightedRowMassNonnegative =
      Shared.markedConstantNonnegative (shared dataSet) Shared.hessianMark
  ; Weighted.WeightedFiniteInfluenceMajorant.weightedRowMassBound =
      weightedGeneratorRowBelowSharedHessian dataSet
  }

weightedGeneratorPowerRowBound :
  ∀ {Scale Volume Root Site}
    (dataSet : SharedMarkedWeightedInfluenceBridge Scale Volume Root Site)
    n x →
  Weighted.weightedPowerRow (asWeightedFiniteInfluence dataSet) n x
  ≤ Power.rationalPower
      (Shared.hessianAnalyticConstant (shared dataSet)) (suc n)
weightedGeneratorPowerRowBound dataSet =
  Weighted.weightedPowerRowBound (asWeightedFiniteInfluence dataSet)

sharedMarkedHessianToWeightedInfluenceLevel : ProofLevel
sharedMarkedHessianToWeightedInfluenceLevel = machineChecked

sharedMarkedHessianToWeightedAllPowerRowsLevel : ProofLevel
sharedMarkedHessianToWeightedAllPowerRowsLevel = machineChecked

-- Highest-alpha physical C-spatial seam: identify the literal absolute
-- derivative generator of the SAME Heat/Doob dynamics with the shared CMP116
-- Hessian mark, retaining the physical exponential weight.  No separate
-- high-order propagation estimate remains after that row comparison.
literalSameDensityWeightedGeneratorBelowSharedHessianLevel : ProofLevel
literalSameDensityWeightedGeneratorBelowSharedHessianLevel = conditional
