{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP23HilbertHaarToR136SignExact where

------------------------------------------------------------------------
-- P2+P3 END-TO-END SIGN COMPILER.
--
-- Physical Haar F^2 positivity
--   -> common-limit Local-C F^2 positivity
--   -> Hilbert trace anomaly negativity
--   -> embedded R136 negativity
--   -> rational R136 negativity.
--
-- Neither the old free trace-frame calibration nor an exact finite=continuum
-- F^2 same-object equality is consumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _<ℝ_)

import DASHI.Physics.Foundations.CMP119CosmologyP2HilbertTraceAnomalyExact as P2
import DASHI.Physics.Foundations.CMP119CosmologyP3LocalCF2PhysicalHaarCommonLimitExact as P3
import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyStandardRealOrderReflectionExact as Order
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as Readout
import DASHI.Physics.Foundations.CMP119AntigravityFiniteToLocalCAnomalyLimitTransportExact as LocalLimit
import DASHI.Physics.Foundations.CMP119AntigravityRealHaarExpectationRepresentationExact as HaarLimit
import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace

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
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as ConcreteLocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119Round109ConcreteLocalCExact as Round109
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local

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
    (selected : R119.CanonicalMetricSelectedStressWeld
      (R134.presentCutCanonicalMetricDomain metricInputs)
      representation coordinate)
    (directions : Continuum.FourAdmittedMetricDirections
      (R134.presentCutCanonicalMetricDomain metricInputs))
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (concreteLocalC :
      ConcreteLocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division} {S = osS}
        osInputs reconstruction group)
    (round109 : Round109.Round109ConcreteLocalCStressWeld Y group concreteLocalC)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : SU2Trace.RealSU2TraceConvention embedding)
    (strict : Strict.RealStrictSignLaws)
    (realOrder : Order.RealStrictOrderAsymmetry)
  where

  physicalHaarF2PositiveForcesNegativeR136 :
    {source :
      P2.HilbertTraceAnomalySource
        recovery selected directions concreteLocalC round109 embedding convention}
    {localTransport :
      LocalLimit.FiniteCMP119ToLocalCAnomalyLimitTransport
        sequenceLimit
        (P2.asSameFamilyLocalCTraceAnomalyReadout
          recovery selected directions concreteLocalC round109 embedding convention source)}
    {physicalHaar : HaarLimit.RealHaarExpectationRepresentation sequenceLimit} →
    (common :
      P3.LocalCF2PhysicalHaarCommonLimit
        (P2.asSameFamilyLocalCTraceAnomalyReadout
          recovery selected directions concreteLocalC round109 embedding convention source)
        localTransport physicalHaar) →
    0ℝ <ℝ HaarLimit.physicalHaarExpectation physicalHaar →
    Continuum.continuumFourDiagonalResponse recovery selected directions < 0ℚ
  physicalHaarF2PositiveForcesNegativeR136
      {source = source} {physicalHaar = physicalHaar}
      common physicalPositive =
    let
      localF2Positive :
        0ℝ <ℝ
          P2.localOperatorNumerator
            recovery selected directions concreteLocalC round109 embedding convention source
            (Local.localOperator
              (P2.localPackage recovery selected directions concreteLocalC round109 embedding convention)
              (P2.fieldStrengthSquarePolynomial
                recovery selected directions concreteLocalC round109 embedding convention source))
      localF2Positive =
        P3.physicalHaarPositiveGivesLocalCF2Positive common physicalPositive

      coefficientNegative :
        SU2Trace.realSU2TraceCoefficient embedding convention <ℝ 0ℝ
      coefficientNegative =
        SU2Trace.realSU2TraceCoefficientNegative strict embedding convention

      hilbertTraceNegative :
        P2.hilbertTraceNumerator
          recovery selected directions concreteLocalC round109 embedding convention
          (ConcreteLocalC.stressTensor concreteLocalC)
        <ℝ 0ℝ
      hilbertTraceNegative =
        subst
          (λ value → value <ℝ 0ℝ)
          (sym
            (P2.hilbertTraceIsSU2BetaF2
              recovery selected directions concreteLocalC round109 embedding convention source))
          (Strict.negativeTimesPositive strict
            coefficientNegative localF2Positive)

      embeddedR136Negative :
        Embed.embed embedding
          (Continuum.continuumFourDiagonalResponse recovery selected directions)
        <ℝ 0ℝ
      embeddedR136Negative =
        subst
          (λ value → value <ℝ 0ℝ)
          (sym
            (P2.embeddedR136IsPinnedLocalCHilbertTrace
              recovery selected directions concreteLocalC round109 embedding convention))
          hilbertTraceNegative
    in
    Readout.reflectNegative
      (Order.negativeOrderReflectionAtZero realOrder embedding)
      (Continuum.continuumFourDiagonalResponse recovery selected directions)
      embeddedR136Negative

  oldTraceFrameCalibrationNotConsumed : Bool
  oldTraceFrameCalibrationNotConsumed = true

  oldExactFiniteContinuumF2WeldNotConsumed : Bool
  oldExactFiniteContinuumF2WeldNotConsumed = true

  p23PreferredSignCompilerUsesHilbertTraceAndCommonLimit : Bool
  p23PreferredSignCompilerUsesHilbertTraceAndCommonLimit = true
