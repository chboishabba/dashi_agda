{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredGaugeFixedEnergyNonnegativeExact where

------------------------------------------------------------------------
-- CONFIGURED PATH4 GAUGE-FIXED ENERGY IS NONNEGATIVE
--
-- This is a pure consequence of existing theorem-bearing finite data:
--   * the physical tangent norm is the positive inner-product square;
--   * the configured coercivity constant is strictly positive;
--   * full gauge-fixed coercivity bounds the energy below by that scaled norm.
-- No T5 measure/observable assumption is used here.
------------------------------------------------------------------------

open import Data.Rational using
  (ℚ; 0ℚ; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate using
  ( configuredPathCoercivityConstant
  ; configuredPathCoercivityConstantPositive
  )
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact using
  (PhysicalSU2Tangent4; physicalUnweightedNormSq)
open import DASHI.Physics.YangMills.BalabanPath4SU2CoarseFineSplittingExact using
  (physicalNormMatchesInner)
open import DASHI.Physics.YangMills.BalabanPath4SU2CompleteGaugeFixedHessianExact using
  (physicalTangentInnerNonnegative)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcretePropagatorExact using
  (configuredGaugeFixedEnergy; configuredGaugeFixedMatrixPositive)

physicalUnweightedNormSqNonnegative : ∀ tangent →
  0ℚ ≤ physicalUnweightedNormSq tangent
physicalUnweightedNormSqNonnegative tangent =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (physicalNormMatchesInner tangent))
    (physicalTangentInnerNonnegative tangent)

scaledPhysicalNormNonnegative : ∀ tangent →
  0ℚ ≤ configuredPathCoercivityConstant * physicalUnweightedNormSq tangent
scaledPhysicalNormNonnegative tangent =
  let
    instance
      coefficientNN : NonNegative configuredPathCoercivityConstant
      coefficientNN =
        nonNegative (ℚP.<⇒≤ configuredPathCoercivityConstantPositive)

      normNN : NonNegative (physicalUnweightedNormSq tangent)
      normNN = nonNegative (physicalUnweightedNormSqNonnegative tangent)
  in
  ℚP.nonNeg*nonNeg⇒nonNeg
    configuredPathCoercivityConstant
    (physicalUnweightedNormSq tangent)

configuredGaugeFixedEnergyNonnegative : ∀ tangent →
  0ℚ ≤ configuredGaugeFixedEnergy tangent
configuredGaugeFixedEnergyNonnegative tangent =
  ℚP.≤-trans
    (scaledPhysicalNormNonnegative tangent)
    (configuredGaugeFixedMatrixPositive tangent)

configuredGaugeFixedEnergyNonnegativeLevel : ProofLevel
configuredGaugeFixedEnergyNonnegativeLevel = machineChecked
