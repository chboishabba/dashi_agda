{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyRealTraceToExpansionMaxCutExact where

------------------------------------------------------------------------
-- REAL TRACE-ANOMALY SIGN -> RATIONAL R136 -> VACUUM ACCELERATION.
--
-- This owner is representation-only.  It does not prove the anomaly theorem;
-- it says that once the negative REAL trace is the same readout as the embedded
-- rational R136 trace, the already-compiled marked-OS vacuum root consumes it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _<ℝ_)

import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as RealBridge
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSMaxCutRootExact as Root
import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanTerminalMaxCutExact as Terminal

import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
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
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC

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
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume RootType ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume RootType ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
  where

  realTraceNegativeForcesLiteralR136TraceNegative :
    (embedding : Embed.OrderedRationalRealEmbedding) →
    (realTrace : ℝ) →
    RealBridge.R136RealTraceReadoutWeld
      embedding
      (Root.literalContinuumTrace recovery selected directions localC)
      realTrace →
    realTrace <ℝ 0ℝ →
    Root.literalContinuumTrace recovery selected directions localC < 0ℚ
  realTraceNegativeForcesLiteralR136TraceNegative
      embedding realTrace weld realNegative =
    RealBridge.realTraceNegativeForcesR136RationalNegative
      weld realNegative

  realTraceNegativeForcesPositiveMatterAcceleration :
    (embedding : Embed.OrderedRationalRealEmbedding) →
    (realTrace : ℝ) →
    (weld :
      RealBridge.R136RealTraceReadoutWeld
        embedding
        (Root.literalContinuumTrace recovery selected directions localC)
        realTrace) →
    (root : Root.MarkedStressOSMaxCutRoot recovery selected directions localC) →
    (positiveGravityFactor : ℚ) →
    0ℚ < positiveGravityFactor →
    realTrace <ℝ 0ℝ →
    0ℚ <
      Vacuum.matterAccelerationContribution
        positiveGravityFactor
        (Terminal.lorentzianIsotropicStress
          (Root.reconstructedTerminalConsequences
            recovery selected directions localC root))
  realTraceNegativeForcesPositiveMatterAcceleration
      embedding realTrace weld root positiveGravityFactor
      factorPositive realNegative =
    Root.rootLiteralContinuumTraceNegativeGivesPositiveMatterAcceleration
      recovery selected directions localC
      positiveGravityFactor root factorPositive
      (realTraceNegativeForcesLiteralR136TraceNegative
        embedding realTrace weld realNegative)

realTraceAnomalyRouteNowFeedsCompiledExpansionConsumer : Bool
realTraceAnomalyRouteNowFeedsCompiledExpansionConsumer = true

remainingAnomalyRepresentationLeafIsSameReadoutWeld : Bool
remainingAnomalyRepresentationLeafIsSameReadoutWeld = true
