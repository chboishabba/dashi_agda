{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR136FiniteWeylConventionWeldExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_)

import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyFiniteWeylConventionFirewallExact as Convention
import DASHI.Physics.Foundations.CMP119CosmologyConventionAwareSectorSignExact as Oriented
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

  r136FourDiagonalResponse : ℚ
  r136FourDiagonalResponse =
    Continuum.continuumFourDiagonalResponse
      recovery selected directions

  record R136FiniteWeylConventionWeld
      {Configuration : Set}
      (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
      (partition : Partition.PhysicalFinitePartitionAuthority measure)
      (d : Source.CompleteFiniteMetricVariation Configuration)
      : Set₁ where
    field
      convention :
        Convention.FiniteWeylToContinuumTraceConvention
          measure partition d r136FourDiagonalResponse

  open R136FiniteWeylConventionWeld public

  r136ResponseNegativeFromExplicitFiniteConvention :
    ∀ {Configuration}
      (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
      (partition : Partition.PhysicalFinitePartitionAuthority measure)
      (d : Source.CompleteFiniteMetricVariation Configuration)
      (laws : Sign.RationalWeylSignIntegrationLaws measure)
      (referenceFixed :
        ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ)
      (weld : R136FiniteWeylConventionWeld measure partition d) →
    Oriented.NegativeOrientedTraceSign
      measure d
      (Convention.orientation (convention weld)) →
    r136FourDiagonalResponse < 0ℚ
  r136ResponseNegativeFromExplicitFiniteConvention
      measure partition d laws referenceFixed weld witness =
    Oriented.continuumTraceNegativeFromExplicitConvention
      measure partition d laws referenceFixed
      r136FourDiagonalResponse
      (convention weld)
      witness

  r136ConventionIsNowSingleExplicitSignLeaf : Bool
  r136ConventionIsNowSingleExplicitSignLeaf = true

  r136FirstVariationAloneDoesNotChooseLogZVersusGamma : Bool
  r136FirstVariationAloneDoesNotChooseLogZVersusGamma = true
