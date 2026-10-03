{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyBalabanVacuumDominatedR136Exact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_; _<_)

import DASHI.Physics.Foundations.CMP119CosmologyBalabanEq223R136SignExact as Preferred
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyVacuumDominatedWeylSignExact as VacuumDominated
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact as Sector
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
    {History Cell : Set} {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    {firstWeld : R133.UnifiedGeneratedActionFirstVariation actionWeld}
    {metricInputs : R134.PresentCutMetricSpecificInputs firstWeld}
    {representation : StressRep.CanonicalMetricStressRepresentation
      (R134.presentCutCanonicalMetricDomain metricInputs)}
    {C : Top.LiteralYangMillsCarriers} {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {lane : StressLane.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      (R134.presentCutCanonicalMetricDomain metricInputs) representation}
    {scaleWeld : R135.UnifiedGeneratedActionStressScale lane}
    (recovery : R136.UnifiedGeneratedActionSectorRecovery scaleWeld)
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected : R119.CanonicalMetricSelectedStressWeld
      (R134.presentCutCanonicalMetricDomain metricInputs)
      representation coordinate)
    (directions : Continuum.FourAdmittedMetricDirections
      (R134.presentCutCanonicalMetricDomain metricInputs))
    {Density Background Fluctuation Action WilsonTerm SmallFieldTerm
     RTerm BoundaryTerm VacuumTerm Configuration : Set}
    {source : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm VacuumTerm}
    {sourceScale : Nat}
    (sourceVariation : Eq223.Eq223SourceMetricVariationRealization
      source Configuration sourceScale)
  where

  d : Source.CompleteFiniteMetricVariation Configuration
  d = Eq223.sourceCompleteFiniteMetricVariation sourceVariation

  literalVacuumConstant : Vacuum.VacuumTraceConstant d
  literalVacuumConstant = Eq223.eq223VacuumTraceConstant sourceVariation

  literalVacuumCoefficient : ℚ
  literalVacuumCoefficient = Eq223.eq223VacuumTraceCoefficient sourceVariation

  literalERBNumerator :
    Physical.PhysicalFiniteYMMeasure Configuration ℚ → ℚ
  literalERBNumerator measure = VacuumDominated.erbNumerator measure d

  literalVacuumDominanceForcesNegativeR136 :
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (scaleLaw : Vacuum.RationalHaarScaleLaw measure)
    (referenceFixed :
      ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ)
    (weld : Preferred.PreferredBalabanR136Weld
      recovery selected directions sourceVariation measure partition) →
    0ℚ < literalVacuumCoefficient →
    0ℚ ≤ literalERBNumerator measure →
    Preferred.r136Response recovery selected directions sourceVariation < 0ℚ
  literalVacuumDominanceForcesNegativeR136
      measure partition laws scaleLaw referenceFixed weld
      vacuumPositive erbNonnegative =
    Preferred.positiveEq223BalanceForcesNegativeR136
      recovery selected directions sourceVariation
      measure partition laws referenceFixed weld
      (VacuumDominated.erbNonnegativeAndVacuumPositiveGivePositiveFourSectorBalance
        measure d erbNonnegative
        (VacuumDominated.vacuumNumeratorPositive
          measure d partition scaleLaw literalVacuumConstant vacuumPositive))

  vacuumCoefficientIsLiteralEq223MetricDerivative : Bool
  vacuumCoefficientIsLiteralEq223MetricDerivative = true

  preferredVacuumDominanceLeavesAreTwoLiteralSectorSigns : Bool
  preferredVacuumDominanceLeavesAreTwoLiteralSectorSigns = true
