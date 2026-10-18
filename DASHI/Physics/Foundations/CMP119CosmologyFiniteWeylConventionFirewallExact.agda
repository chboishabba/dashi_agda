{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyFiniteWeylConventionFirewallExact where

------------------------------------------------------------------------
-- FINITE WEYL SIGN CONVENTION FIREWALL.
--
-- Three distinct quantities must not be conflated:
--
--   W_Z      = sum_mu D_mu Z
--   W_logZ   = (sum_mu D_mu Z) / Z
--   W_Gamma  = - (sum_mu D_mu Z) / Z       for Gamma = - log Z.
--
-- The existing finite sign owner proves a sign for W_Z.
-- A gravitational stress tensor obtained from variation of Gamma inherits the
-- OPPOSITE sign after division by the strictly positive partition function.
--
-- This module does not choose whether the repository's R136 rational readout
-- represents +D log Z, -D log Z, 2/sqrt(g) delta Gamma/delta g, or another
-- normalized convention.  It forces that orientation to be stated explicitly
-- before a finite partition-response sign is transported into cosmology.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; Positive; _*_; _<_; -_; positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyPartitionWeylTraceExact as Weyl
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quot

partitionWeylDerivative :
  ∀ {Configuration} →
  Physical.PhysicalFiniteYMMeasure Configuration ℚ →
  Source.CompleteFiniteMetricVariation Configuration →
  ℚ
partitionWeylDerivative =
  Weyl.fourDiagonalPartitionDerivativeSum

logPartitionWeylResponse :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) →
  Partition.PhysicalFinitePartitionAuthority measure →
  Source.CompleteFiniteMetricVariation Configuration →
  ℚ
logPartitionWeylResponse measure authority d =
  Quot.dividePositive
    (partitionWeylDerivative measure d)
    (Physical.partitionFunction measure)
    (Partition.partitionPositive authority)

matterEffectiveActionWeylResponse :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) →
  Partition.PhysicalFinitePartitionAuthority measure →
  Source.CompleteFiniteMetricVariation Configuration →
  ℚ
matterEffectiveActionWeylResponse measure authority d =
  - logPartitionWeylResponse measure authority d

matterEffectiveActionWeylIsNegativeLogPartitionWeyl :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (authority : Partition.PhysicalFinitePartitionAuthority measure)
    (d : Source.CompleteFiniteMetricVariation Configuration) →
  matterEffectiveActionWeylResponse measure authority d
  ≡ - logPartitionWeylResponse measure authority d
matterEffectiveActionWeylIsNegativeLogPartitionWeyl measure authority d =
  refl

partitionWeylNegativeImpliesLogPartitionWeylNegative :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (authority : Partition.PhysicalFinitePartitionAuthority measure)
    (d : Source.CompleteFiniteMetricVariation Configuration) →
  partitionWeylDerivative measure d < 0ℚ →
  logPartitionWeylResponse measure authority d < 0ℚ
partitionWeylNegativeImpliesLogPartitionWeylNegative
    measure authority d partitionNegative =
  let
    z = Physical.partitionFunction measure
    zPositive = Partition.partitionPositive authority
    reciprocal = Quot.positiveReciprocal z zPositive
    reciprocalPositive = Quot.positiveReciprocalPositive z zPositive

    instance
      reciprocalPositiveI : Positive reciprocal
      reciprocalPositiveI = positive reciprocalPositive

    scaled :
      partitionWeylDerivative measure d * reciprocal
      < 0ℚ * reciprocal
    scaled =
      ℚP.*-monoʳ-<-pos reciprocal partitionNegative
  in
  subst
    (λ right → logPartitionWeylResponse measure authority d < right)
    (Ring.solve-∀ reciprocal)
    scaled

partitionWeylNegativeImpliesEffectiveActionWeylPositive :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (authority : Partition.PhysicalFinitePartitionAuthority measure)
    (d : Source.CompleteFiniteMetricVariation Configuration) →
  partitionWeylDerivative measure d < 0ℚ →
  0ℚ < matterEffectiveActionWeylResponse measure authority d
partitionWeylNegativeImpliesEffectiveActionWeylPositive
    measure authority d partitionNegative =
  let
    logNegative =
      partitionWeylNegativeImpliesLogPartitionWeylNegative
        measure authority d partitionNegative
    reversed :
      - 0ℚ < - logPartitionWeylResponse measure authority d
    reversed =
      ℚP.neg-antimono-< logNegative
  in
  subst
    (λ left → left < matterEffectiveActionWeylResponse measure authority d)
    (Ring.solve [])
    reversed

partitionWeylPositiveImpliesLogPartitionWeylPositive :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (authority : Partition.PhysicalFinitePartitionAuthority measure)
    (d : Source.CompleteFiniteMetricVariation Configuration) →
  0ℚ < partitionWeylDerivative measure d →
  0ℚ < logPartitionWeylResponse measure authority d
partitionWeylPositiveImpliesLogPartitionWeylPositive
    measure authority d partitionPositive =
  let
    z = Physical.partitionFunction measure
    zPositive = Partition.partitionPositive authority
    reciprocal = Quot.positiveReciprocal z zPositive
    reciprocalPositive = Quot.positiveReciprocalPositive z zPositive

    instance
      reciprocalPositiveI : Positive reciprocal
      reciprocalPositiveI = positive reciprocalPositive

    scaled :
      0ℚ * reciprocal
      < partitionWeylDerivative measure d * reciprocal
    scaled =
      ℚP.*-monoʳ-<-pos reciprocal partitionPositive
  in
  subst
    (λ left → left < logPartitionWeylResponse measure authority d)
    (Ring.solve-∀ reciprocal)
    scaled

partitionWeylPositiveImpliesEffectiveActionWeylNegative :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (authority : Partition.PhysicalFinitePartitionAuthority measure)
    (d : Source.CompleteFiniteMetricVariation Configuration) →
  0ℚ < partitionWeylDerivative measure d →
  matterEffectiveActionWeylResponse measure authority d < 0ℚ
partitionWeylPositiveImpliesEffectiveActionWeylNegative
    measure authority d partitionPositive =
  let
    logPositive =
      partitionWeylPositiveImpliesLogPartitionWeylPositive
        measure authority d partitionPositive
    reversed :
      - logPartitionWeylResponse measure authority d < - 0ℚ
    reversed =
      ℚP.neg-antimono-< logPositive
  in
  subst
    (λ right → matterEffectiveActionWeylResponse measure authority d < right)
    (Ring.solve [])
    reversed

data FiniteToContinuumWeylOrientation : Set where
  continuumReadsLogPartitionResponse :
    FiniteToContinuumWeylOrientation
  continuumReadsMatterEffectiveActionResponse :
    FiniteToContinuumWeylOrientation

orientedFiniteWeylResponse :
  ∀ {Configuration} →
  FiniteToContinuumWeylOrientation →
  (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) →
  Partition.PhysicalFinitePartitionAuthority measure →
  Source.CompleteFiniteMetricVariation Configuration →
  ℚ
orientedFiniteWeylResponse
    continuumReadsLogPartitionResponse measure authority d =
  logPartitionWeylResponse measure authority d
orientedFiniteWeylResponse
    continuumReadsMatterEffectiveActionResponse measure authority d =
  matterEffectiveActionWeylResponse measure authority d

record FiniteWeylToContinuumTraceConvention
    {Configuration : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (authority : Partition.PhysicalFinitePartitionAuthority measure)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (continuumTrace : ℚ)
    : Set₁ where
  field
    orientation : FiniteToContinuumWeylOrientation

    selectedOrientationIsCorrect :
      continuumTrace
      ≡ orientedFiniteWeylResponse orientation measure authority d

open FiniteWeylToContinuumTraceConvention public

partitionDerivativeSignIsNotYetStressTraceSign : Bool
partitionDerivativeSignIsNotYetStressTraceSign = true

effectiveActionResponseHasOppositeOrientationToLogPartition : Bool
effectiveActionResponseHasOppositeOrientationToLogPartition = true

r136TraceRequiresExplicitFiniteConventionWeld : Bool
r136TraceRequiresExplicitFiniteConventionWeld = true
