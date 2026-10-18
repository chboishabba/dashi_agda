{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyNormalizedSectorWeylResponseExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _<_; -_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyFiniteWeylConventionFirewallExact as Convention
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quot

normalizedNonWilsonWeylNumerator :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) →
  Partition.PhysicalFinitePartitionAuthority measure →
  Source.CompleteFiniteMetricVariation Configuration → ℚ
normalizedNonWilsonWeylNumerator measure partition d =
  Quot.dividePositive
    (Sign.weightedNonWilsonWeylNumerator measure d)
    (Physical.partitionFunction measure)
    (Partition.partitionPositive partition)

finiteGammaWeylIsNormalizedNonWilsonNumerator :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (referenceFixed :
      ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ) →
  Convention.matterEffectiveActionWeylResponse measure partition d
  ≡ normalizedNonWilsonWeylNumerator measure partition d
finiteGammaWeylIsNormalizedNonWilsonNumerator
    measure d laws partition referenceFixed =
  let
    responseEquality =
      Sign.fixedHaarResponseIsNegativeWeightedNonWilsonNumerator
        measure d laws referenceFixed

    z = Physical.partitionFunction measure
    zPositive = Partition.partitionPositive partition
    n = Sign.weightedNonWilsonWeylNumerator measure d
    reciprocal = Quot.positiveReciprocal z zPositive
  in
  trans
    (cong -_
      (cong
        (λ numerator → Quot.dividePositive numerator z zPositive)
        responseEquality))
    (Ring.solve-∀ n reciprocal)

normalizedSectorMarginForcesFiniteGammaNegative :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (referenceFixed :
      ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ)
    margin →
  normalizedNonWilsonWeylNumerator measure partition d + margin < 0ℚ →
  Convention.matterEffectiveActionWeylResponse measure partition d + margin
    < 0ℚ
normalizedSectorMarginForcesFiniteGammaNegative
    measure d laws partition referenceFixed margin sectorMargin =
  subst
    (λ value → value + margin < 0ℚ)
    (finiteGammaWeylIsNormalizedNonWilsonNumerator
      measure d laws partition referenceFixed)
    sectorMargin

finiteGammaSignAndMarginNowOwnedByNormalizedSectorNumerator : Bool
finiteGammaSignAndMarginNowOwnedByNormalizedSectorNumerator = true
