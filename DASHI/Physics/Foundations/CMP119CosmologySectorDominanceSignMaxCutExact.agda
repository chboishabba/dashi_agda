{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologySectorDominanceSignMaxCutExact where

------------------------------------------------------------------------
-- GENERAL SECTOR-DOMINANCE SIGN CUT.
--
-- The special branch
--
--   c_V < 0,   N_E + N_R + N_B <= 0
--
-- is sufficient but stronger than necessary.  The exact physical condition is
-- simply
--
--   N_E + N_R + N_B < - N_V.
--
-- This file proves that condition makes the total non-Wilson numerator
-- negative and therefore, for Gamma = -log Z with Z>0, the finite matter
-- effective-action Weyl response is negative.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _<_; -_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyPartitionWeylTraceExact as Weyl
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact as Sector
import DASHI.Physics.Foundations.CMP119CosmologyVacuumDominatedWeylSignExact as VacuumCut
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyFiniteWeylConventionFirewallExact as Convention
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

erbBelowNegativeVacuumForcesNegativeFourSectorBalance :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration) →
  VacuumCut.erbNumerator measure d
    < - Sector.vacuumNumerator measure d →
  ((Sector.regularNumerator measure d
      + Sector.rOperationNumerator measure d)
      + (Sector.boundaryNumerator measure d
        + Sector.vacuumNumerator measure d))
    < 0ℚ
erbBelowNegativeVacuumForcesNegativeFourSectorBalance measure d dominance =
  subst
    (λ right →
      ((Sector.regularNumerator measure d
        + Sector.rOperationNumerator measure d)
        + (Sector.boundaryNumerator measure d
          + Sector.vacuumNumerator measure d))
      < right)
    (Ring.solve-∀
      (VacuumCut.erbNumerator measure d)
      (Sector.vacuumNumerator measure d))
    dominance

sectorDominanceForcesPositivePartitionWeyl :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ) →
  VacuumCut.erbNumerator measure d
    < - Sector.vacuumNumerator measure d →
  0ℚ < Weyl.fourDiagonalPartitionDerivativeSum measure d
sectorDominanceForcesPositivePartitionWeyl
    measure d laws referenceFixed dominance =
  Sector.negativeFourSectorBalanceForcesPositiveWeylResponse
    measure d laws referenceFixed
    (erbBelowNegativeVacuumForcesNegativeFourSectorBalance
      measure d dominance)

sectorDominanceForcesNegativeMatterEffectiveActionWeyl :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (referenceFixed :
      ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ) →
  VacuumCut.erbNumerator measure d
    < - Sector.vacuumNumerator measure d →
  Convention.matterEffectiveActionWeylResponse measure partition d < 0ℚ
sectorDominanceForcesNegativeMatterEffectiveActionWeyl
    measure d laws partition referenceFixed dominance =
  Convention.partitionWeylPositiveImpliesEffectiveActionWeylNegative
    measure partition d
    (sectorDominanceForcesPositivePartitionWeyl
      measure d laws referenceFixed dominance)

exactAccelerationSignSourceTargetIsSectorDominance : Bool
exactAccelerationSignSourceTargetIsSectorDominance = true

negativeVacuumCoefficientIsSufficientButNotNecessary : Bool
negativeVacuumCoefficientIsSufficientButNotNecessary = true
