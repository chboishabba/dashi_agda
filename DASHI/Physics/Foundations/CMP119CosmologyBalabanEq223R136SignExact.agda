{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyBalabanEq223R136SignExact where

------------------------------------------------------------------------
-- PREFERRED SOURCE SIGN ROOT.
--
-- Balaban source convention fixes +D log Z.  Therefore a POSITIVE literal
-- E/R/B/V weighted Weyl numerator is the sign required for a negative R136
-- continuum response.  The only convention weld retained is same-object:
-- R136 continuum first variation = exact normalized finite log-weight response.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_)

import DASHI.Physics.Foundations.CMP119CosmologyBalabanLogWeightOrientationExact as Balaban
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyR136FiniteWeylConventionWeldExact as R136Convention
import DASHI.Physics.Foundations.CMP119CosmologyConventionAwareSectorSignExact as Oriented
import DASHI.Physics.Foundations.CMP119CosmologyFiniteWeylConventionFirewallExact as Convention
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum

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
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

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
    {Density Background Fluctuation Action WilsonTerm SmallFieldTerm
     RTerm BoundaryTerm Vacuum Configuration : Set}
    {source :
      Raw.CMP119SourceNativeRawState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    {sourceScale : Nat}
    (sourceVariation :
      Eq223.Eq223SourceMetricVariationRealization
        source Configuration sourceScale)
  where

  d : Source.CompleteFiniteMetricVariation Configuration
  d = Eq223.sourceCompleteFiniteMetricVariation sourceVariation

  r136Response : ℚ
  r136Response =
    R136Convention.r136FourDiagonalResponse recovery selected directions

  record PreferredBalabanR136Weld
      (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
      (partition : Partition.PhysicalFinitePartitionAuthority measure)
      : Set₁ where
    field
      logWeightWeld :
        Balaban.BalabanLogWeightContinuumWeld
          measure partition d r136Response

  open PreferredBalabanR136Weld public

  asR136ConventionWeld :
    ∀ {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
      {partition : Partition.PhysicalFinitePartitionAuthority measure} →
    PreferredBalabanR136Weld measure partition →
    R136Convention.R136FiniteWeylConventionWeld
      recovery selected directions measure partition d
  asR136ConventionWeld weld = record
    { R136Convention.R136FiniteWeylConventionWeld.convention =
        Balaban.asFiniteWeylToContinuumConvention (logWeightWeld weld)
    }

  positiveEq223BalanceForcesNegativeR136 :
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ)
    (weld : PreferredBalabanR136Weld measure partition) →
    0ℚ < Oriented.fourSectorBalance measure d →
    r136Response < 0ℚ
  positiveEq223BalanceForcesNegativeR136
      measure partition laws referenceFixed weld balancePositive =
    R136Convention.r136ResponseNegativeFromExplicitFiniteConvention
      recovery selected directions
      measure partition d laws referenceFixed
      (asR136ConventionWeld weld)
      (Oriented.logPartitionNeedsPositiveSectorBalance balancePositive)

  preferredSignLeafIsPositiveEq223Balance : Bool
  preferredSignLeafIsPositiveEq223Balance = true

  gammaMinusLogZBranchRemovedFromPreferredSourceScheduler : Bool
  gammaMinusLogZBranchRemovedFromPreferredSourceScheduler = true
