{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223EffectiveActionToExpansionMaxCutExact where

------------------------------------------------------------------------
-- CORRECTED PREFERRED END-TO-END SIGN COMPILER.
--
--   literal Eq.(2.23) dominance N_ERB < -N_V
--   + same-object Q_R136 = D_Gamma Weyl response
--   + marked-OS vacuum reconstruction
--   + positive gravitational prefactor
--   ------------------------------------------------
--   positive matter acceleration contribution.
--
-- This is the gravitational one-point lane.  It does not use the blocked-action
-- +D log(weight) orientation as the stress observable.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_; -_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.CMP119CosmologyEq223CombinedERBEnvelopeMaxCutExact as Envelope
import DASHI.Physics.Foundations.CMP119CosmologyEq223EffectiveActionR136MaxCutExact as Preferred
import DASHI.Physics.Foundations.CMP119CosmologyEq223NegativeSectorDominanceExact as Eq223Sign
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSMaxCutRootExact as Root
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as VacuumFactor
import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanTerminalMaxCutExact as Terminal
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureOrderExact as Order

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
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
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
    {G X LocalConfiguration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume RootType ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X LocalConfiguration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume RootType ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
    {Density Background Fluctuation
     Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm
     Configuration : Set}
    {source :
      Raw.CMP119SourceNativeRawState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm}
    {sourceScale : Nat}
    (sourceVariation :
      Eq223.Eq223SourceMetricVariationRealization
        source Configuration sourceScale)
  where

  r136Response : ℚ
  r136Response = Continuum.continuumFourDiagonalResponse recovery selected directions

  literalTrace : ℚ
  literalTrace = Root.literalContinuumTrace recovery selected directions localC

  r136NegativeGivesLiteralTraceNegative :
    r136Response < 0ℚ → literalTrace < 0ℚ
  r136NegativeGivesLiteralTraceNegative r136Negative =
    subst
      (λ value → value < 0ℚ)
      (Continuum.continuumFourDiagonalResponseIsLiteralStressPairing
        recovery selected directions)
      r136Negative

  literalEq223DominanceForcesPositiveMatterAcceleration :
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x →
      Source.referenceMeasureLogVariation
        (Eq223.sourceCompleteFiniteMetricVariation sourceVariation) h x
      ≡ 0ℚ)
    (responseWeld :
      Preferred.R136EffectiveActionResponseWeld
        recovery selected directions sourceVariation measure partition)
    (dominance :
      Eq223Sign.LiteralNegativeSectorDominance sourceVariation measure)
    (root : Root.MarkedStressOSMaxCutRoot recovery selected directions localC)
    (positiveGravityFactor : ℚ) →
    0ℚ < positiveGravityFactor →
    0ℚ <
      Vacuum.matterAccelerationContribution
        positiveGravityFactor
        (Terminal.lorentzianIsotropicStress
          (Root.reconstructedTerminalConsequences
            recovery selected directions localC root))
  literalEq223DominanceForcesPositiveMatterAcceleration
      measure partition laws referenceFixed responseWeld dominance
      root positiveGravityFactor factorPositive =
    Root.rootLiteralContinuumTraceNegativeGivesPositiveMatterAcceleration
      recovery selected directions localC
      positiveGravityFactor root factorPositive
      (r136NegativeGivesLiteralTraceNegative
        (Preferred.literalDominanceForcesNegativeR136
          recovery selected directions sourceVariation
          measure partition laws referenceFixed responseWeld dominance))

  combinedEnvelopeMarginForcesPositiveMatterAcceleration :
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (orderLaws : Order.RationalPositiveFiniteMeasureOrderLaws measure)
    (scaleLaw : VacuumFactor.RationalHaarScaleLaw measure)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x →
      Source.referenceMeasureLogVariation
        (Eq223.sourceCompleteFiniteMetricVariation sourceVariation) h x
      ≡ 0ℚ)
    (responseWeld :
      Preferred.R136EffectiveActionResponseWeld
        recovery selected directions sourceVariation measure partition)
    (envelope :
      Envelope.CombinedERBTraceEnvelope
        sourceVariation measure orderLaws partition scaleLaw)
    (sourceMargin :
      Envelope.combinedUpper envelope
        < - Eq223.eq223VacuumTraceCoefficient sourceVariation)
    (root : Root.MarkedStressOSMaxCutRoot recovery selected directions localC)
    (positiveGravityFactor : ℚ) →
    0ℚ < positiveGravityFactor →
    0ℚ <
      Vacuum.matterAccelerationContribution
        positiveGravityFactor
        (Terminal.lorentzianIsotropicStress
          (Root.reconstructedTerminalConsequences
            recovery selected directions localC root))
  combinedEnvelopeMarginForcesPositiveMatterAcceleration
      measure partition orderLaws scaleLaw laws referenceFixed responseWeld
      envelope sourceMargin root positiveGravityFactor factorPositive =
    Root.rootLiteralContinuumTraceNegativeGivesPositiveMatterAcceleration
      recovery selected directions localC
      positiveGravityFactor root factorPositive
      (r136NegativeGivesLiteralTraceNegative
        (Preferred.combinedEnvelopeMarginForcesNegativeR136
          recovery selected directions sourceVariation
          measure partition orderLaws scaleLaw laws referenceFixed responseWeld
          envelope sourceMargin))

  correctedEffectiveActionRouteCompilesEndToEnd : Bool
  correctedEffectiveActionRouteCompilesEndToEnd = true

  combinedEq223EnvelopeRouteCompilesEndToEnd : Bool
  combinedEq223EnvelopeRouteCompilesEndToEnd = true
