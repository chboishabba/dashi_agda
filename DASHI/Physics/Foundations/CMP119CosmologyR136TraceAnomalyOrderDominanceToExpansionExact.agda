{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR136TraceAnomalyOrderDominanceToExpansionExact where

------------------------------------------------------------------------
-- ALTERNATE ANOMALY ROUTE WITH ONE-SIDED SAME-OBJECT DOMINANCE.
--
-- The selected physical anomaly trace is strictly negative.  Exact equality
-- with the embedded R136 response is unnecessary: it is enough to prove
--
--   embed Q_R136 <= selected anomaly trace.
--
-- Standard real weak/strict transitivity plus negative-order reflection gives
-- Q_R136 < 0, after which the existing marked-OS terminal compiler gives the
-- positive matter-acceleration contribution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.CMP119CosmologyR136TraceAnomalyOrderDominanceExact as Dominance
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as Order
import DASHI.Physics.Foundations.CMP119CosmologySelectedR109RealTailSignCompilerExact as RealOrder
import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSMaxCutRootExact as Root
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanTerminalMaxCutExact as Terminal
import DASHI.Physics.Foundations.CMP119AntigravityRealPhysicalTraceAnomalyCapstoneExact as Capstone
import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as GibbsPositive
import DASHI.Physics.Foundations.CMP119AntigravityRealFullSupportHaarExact as FullSupport

import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as Gibbs
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

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
  where

  r136Response : ℚ
  r136Response =
    Continuum.continuumFourDiagonalResponse recovery selected directions

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

  anomalyOrderDominanceForcesPositiveMatterAcceleration :
    ∀ {PhysicalConfiguration Action}
      {realAlgebra : Cylinder.ScalarCylinderLimitAlgebra ℝ}
      {quotientAuthority :
        Quotient.RealQuotientConvergenceAuthority
          (Cylinder.Converges realAlgebra)}
      (realDivision : Division.RealDivisionAlgebra realAlgebra quotientAuthority)
      {measure : Physical.PhysicalFiniteYMMeasure PhysicalConfiguration ℝ}
      (laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure)
      (strict : Strict.RealStrictSignLaws)
      (embedding : Embed.OrderedRationalRealEmbedding)
      (realOrder : RealOrder.RealWeakStrictTransitivity)
      (reflection : Order.NegativeOrderReflectionAtZero embedding)
      (convention : Trace.RealSU2TraceConvention embedding)
      (gibbs :
        Gibbs.WilsonGibbsHaarAction
          {Configuration = PhysicalConfiguration} {Action = Action}
          measure laws)
      (exponential : GibbsPositive.StrictPositiveRealExponential)
      (fullSupport : FullSupport.FullSupportRealHaarAuthority measure)
      (input :
        Capstone.RealPhysicalTraceAnomalyInput
          realAlgebra quotientAuthority realDivision laws strict embedding convention
          gibbs exponential fullSupport)
      (weld :
        Dominance.R136ToRealTraceAnomalyUpperWeld
          realDivision laws strict embedding convention gibbs exponential fullSupport
          input r136Response)
      (root : Root.MarkedStressOSMaxCutRoot recovery selected directions localC)
      (positiveGravityFactor : ℚ) →
    0ℚ < positiveGravityFactor →
    0ℚ <
      Vacuum.matterAccelerationContribution
        positiveGravityFactor
        (Terminal.lorentzianIsotropicStress
          (Root.reconstructedTerminalConsequences
            recovery selected directions localC root))
  anomalyOrderDominanceForcesPositiveMatterAcceleration
      realDivision laws strict embedding realOrder reflection convention gibbs exponential
      fullSupport input weld root positiveGravityFactor factorPositive =
    Root.rootLiteralContinuumTraceNegativeGivesPositiveMatterAcceleration
      recovery selected directions localC
      positiveGravityFactor root factorPositive
      (r136NegativeGivesLiteralTraceNegative
        (Dominance.rationalR136NegativeFromUpperWeld
          realDivision laws strict embedding realOrder reflection convention gibbs exponential
          fullSupport input r136Response weld))

anomalyOrderDominanceNowCompilesToMatterAcceleration : Bool
anomalyOrderDominanceNowCompilesToMatterAcceleration = true

remainingAlternateSignLeafIsOneSidedR136AnomalyDominance : Bool
remainingAlternateSignLeafIsOneSidedR136AnomalyDominance = true
