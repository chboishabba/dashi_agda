{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyConventionAwareSectorSignExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact as Sector
import DASHI.Physics.Foundations.CMP119CosmologyFiniteWeylConventionFirewallExact as Convention
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

fourSectorBalance :
  ∀ {Configuration} →
  Physical.PhysicalFiniteYMMeasure Configuration ℚ →
  Source.CompleteFiniteMetricVariation Configuration →
  ℚ
fourSectorBalance measure d =
  (Sector.regularNumerator measure d + Sector.rOperationNumerator measure d)
  + (Sector.boundaryNumerator measure d + Sector.vacuumNumerator measure d)

data NegativeOrientedTraceSign
    {Configuration : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    : Convention.FiniteToContinuumWeylOrientation → Set where

  logPartitionNeedsPositiveSectorBalance :
    0ℚ < fourSectorBalance measure d →
    NegativeOrientedTraceSign measure d
      Convention.continuumReadsLogPartitionResponse

  effectiveActionNeedsNegativeSectorBalance :
    fourSectorBalance measure d < 0ℚ →
    NegativeOrientedTraceSign measure d
      Convention.continuumReadsMatterEffectiveActionResponse

orientedFiniteResponseNegative :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (authority : Partition.PhysicalFinitePartitionAuthority measure)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ)
    (orientation : Convention.FiniteToContinuumWeylOrientation) →
  NegativeOrientedTraceSign measure d orientation →
  Convention.orientedFiniteWeylResponse
    orientation measure authority d
  < 0ℚ
orientedFiniteResponseNegative
    measure authority d laws referenceFixed
    Convention.continuumReadsLogPartitionResponse
    (logPartitionNeedsPositiveSectorBalance balancePositive) =
  Convention.partitionWeylNegativeImpliesLogPartitionWeylNegative
    measure authority d
    (Sector.positiveFourSectorBalanceForcesNegativeWeylResponse
      measure d laws referenceFixed balancePositive)
orientedFiniteResponseNegative
    measure authority d laws referenceFixed
    Convention.continuumReadsMatterEffectiveActionResponse
    (effectiveActionNeedsNegativeSectorBalance balanceNegative) =
  Convention.partitionWeylPositiveImpliesEffectiveActionWeylNegative
    measure authority d
    (Sector.negativeFourSectorBalanceForcesPositiveWeylResponse
      measure d laws referenceFixed balanceNegative)

continuumTraceNegativeFromExplicitConvention :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (authority : Partition.PhysicalFinitePartitionAuthority measure)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ)
    (continuumTrace : ℚ)
    (convention :
      Convention.FiniteWeylToContinuumTraceConvention
        measure authority d continuumTrace) →
  NegativeOrientedTraceSign
    measure d (Convention.orientation convention) →
  continuumTrace < 0ℚ
continuumTraceNegativeFromExplicitConvention
    measure authority d laws referenceFixed continuumTrace convention witness =
  subst
    (λ value → value < 0ℚ)
    (sym (Convention.selectedOrientationIsCorrect convention))
    (orientedFiniteResponseNegative
      measure authority d laws referenceFixed
      (Convention.orientation convention) witness)

signTargetDependsOnFiniteToContinuumOrientation : Bool
signTargetDependsOnFiniteToContinuumOrientation = true

negativeContinuumTraceCannotBeClaimedBeforeConventionWeld : Bool
negativeContinuumTraceCannotBeClaimedBeforeConventionWeld = true
