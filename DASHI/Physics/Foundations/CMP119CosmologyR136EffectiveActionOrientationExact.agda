{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR136EffectiveActionOrientationExact where

------------------------------------------------------------------------
-- R136 ONE-POINT GRAVITATIONAL STRESS USES D_Gamma, NOT +D log Z.
--
-- The finite R144 stress owner defines
--
--   Gamma = - log Z,
--   D_Gamma[h] = - D Z[h] / Z,
--
-- and proves this is the normalized expectation of the selected CMP119
-- action/stress insertion.  Consequently the Eq.(2.23) sector sign required
-- for a NEGATIVE R136 one-point trace is the opposite of the raw +D log Z
-- sign:
--
--   N_nonWilson < 0
--       =>  W_Z > 0
--       =>  D_Gamma = - W_Z / Z < 0.
--
-- This owner makes that gravitational orientation explicit on the ACTUAL R136
-- four-diagonal response.  It deliberately does not erase the older +D log Z
-- convention: that convention remains useful for Balaban's blocked log weight,
-- but it is not the finite one-point gravitational stress convention.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyFiniteWeylConventionFirewallExact as Convention
import DASHI.Physics.Foundations.CMP119CosmologyR136FiniteWeylConventionWeldExact as R136Convention
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact as Sector
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as StressLane
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133
import DASHI.Physics.YangMills.BalabanPresentCutCanonicalMetricDomainRound134Exact as R134
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionStressScaleRound135Exact as R135
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionRecoveryRound136Exact as R136
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

module _
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set}
    {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    {firstWeld : R133.UnifiedGeneratedActionFirstVariation actionWeld}
    {metricInputs : R134.PresentCutMetricSpecificInputs firstWeld}
    {representation : StressRep.CanonicalMetricStressRepresentation
      (R134.presentCutCanonicalMetricDomain metricInputs)}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {lane : StressLane.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      (R134.presentCutCanonicalMetricDomain metricInputs) representation}
    {scaleWeld : R135.UnifiedGeneratedActionStressScale lane}
    (recovery : R136.UnifiedGeneratedActionSectorRecovery scaleWeld)
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        (R134.presentCutCanonicalMetricDomain metricInputs)
        representation coordinate)
    (directions :
      Continuum.FourAdmittedMetricDirections
        (R134.presentCutCanonicalMetricDomain metricInputs))
  where

  record R136EffectiveActionOrientationWeld
      {Configuration : Set}
      (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
      (partition : Partition.PhysicalFinitePartitionAuthority measure)
      (d : Source.CompleteFiniteMetricVariation Configuration)
      : Set₁ where
    field
      r136IsEffectiveActionResponse :
        R136Convention.r136FourDiagonalResponse
          recovery selected directions
        ≡ Convention.matterEffectiveActionWeylResponse
            measure partition d

  open R136EffectiveActionOrientationWeld public

  negativeFourSectorBalanceForcesNegativeR136EffectiveAction :
    ∀ {Configuration}
      (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
      (partition : Partition.PhysicalFinitePartitionAuthority measure)
      (d : Source.CompleteFiniteMetricVariation Configuration)
      (laws : Sign.RationalWeylSignIntegrationLaws measure)
      (referenceFixed :
        ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ)
      (weld : R136EffectiveActionOrientationWeld measure partition d) →
    ((Sector.regularNumerator measure d + Sector.rOperationNumerator measure d)
      + (Sector.boundaryNumerator measure d + Sector.vacuumNumerator measure d))
      < 0ℚ →
    R136Convention.r136FourDiagonalResponse recovery selected directions < 0ℚ
  negativeFourSectorBalanceForcesNegativeR136EffectiveAction
      measure partition d laws referenceFixed weld balanceNegative =
    let
      partitionPositive =
        Sector.negativeFourSectorBalanceForcesPositiveWeylResponse
          measure d laws referenceFixed balanceNegative

      effectiveNegative =
        Convention.partitionWeylPositiveImpliesEffectiveActionWeylNegative
          measure partition d partitionPositive
    in
    subst
      (λ value → value < 0ℚ)
      (sym (r136IsEffectiveActionResponse weld))
      effectiveNegative

  gravitationalOnePointOrientationIsDGamma : Bool
  gravitationalOnePointOrientationIsDGamma = true

  gravitationalOnePointOrientationIsPlusDLogZ : Bool
  gravitationalOnePointOrientationIsPlusDLogZ = false

  preferredEq223SignForNegativeR136IsNegativeBalance : Bool
  preferredEq223SignForNegativeR136IsNegativeBalance = true

  positiveEq223BalanceWouldGiveOppositeDGammaSign : Bool
  positiveEq223BalanceWouldGiveOppositeDGammaSign = true
