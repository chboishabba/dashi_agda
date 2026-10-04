{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPinnedLocalCAnomalyToExpansionMaxCutExact where

------------------------------------------------------------------------
-- END-TO-END ANOMALY ROUTE.
--
-- This specializes the generic real-trace consumer to the ACTUAL concrete
-- pinned Local-C package used by the cosmology root:
--
--   physical weighted F^2 > 0
--     + same-object Local-C anomaly transport
--     + Local-C real trace = embedded R136 trace
--     + marked OS vacuum root
--   ------------------------------------------------
--     positive matter acceleration contribution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyPinnedLocalCRealTraceSignExact as TraceSign
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as RealBridge
import DASHI.Physics.Foundations.CMP119CosmologyRealTraceToExpansionMaxCutExact as RealToExpansion
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSMaxCutRootExact as Root
import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanTerminalMaxCutExact as Terminal
import DASHI.Physics.Foundations.CMP119AntigravityConcreteLocalCAnomalyTransportExact as Transport
import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealF2StrictPositivityFromFullSupportExact as F2Positive
import DASHI.Physics.Foundations.CMP119AntigravityRealFullSupportHaarExact as FullSupport
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as GibbsPositive

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
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as Gibbs

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

  localPackage = LocalC.compileConcretePinnedLocalPackage localC

  anomalyTrace :
    ∀ {embedding convention}
      (transport :
        Transport.ConcreteLocalCAntigravityAnomalyTransport
          localPackage embedding convention) → ℝ
  anomalyTrace transport =
    Transport.stressTraceNumerator transport
      (Local.stressTensor localPackage)

  pinnedAnomalyForcesPositiveMatterAcceleration :
    ∀ {PhysicalConfiguration Action}
      {embedding : Embed.OrderedRationalRealEmbedding}
      {convention : Trace.RealSU2TraceConvention embedding}
      {transport :
        Transport.ConcreteLocalCAntigravityAnomalyTransport
          localPackage embedding convention}
      {measure : Physical.PhysicalFiniteYMMeasure PhysicalConfiguration ℝ}
      {laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure}
      {strict : Strict.RealStrictSignLaws}
      {gibbs :
        Gibbs.WilsonGibbsHaarAction
          {Configuration = PhysicalConfiguration} {Action = Action}
          measure laws}
      {exponential : GibbsPositive.StrictPositiveRealExponential}
      {fullSupport : FullSupport.FullSupportRealHaarAuthority measure}
      {f2Positivity :
        F2Positive.RealPhysicalF2StrictPositivityInput
          strict embedding gibbs exponential fullSupport} →
    (f2Weld :
      TraceSign.PinnedLocalCPhysicalF2Weld
        {localC = localPackage}
        {embedding = embedding} {convention = convention}
        transport
        {measure = measure} {laws = laws} {strict = strict}
        {gibbs = gibbs} {exponential = exponential}
        {fullSupport = fullSupport} f2Positivity) →
    (readoutWeld :
      RealBridge.R136RealTraceReadoutWeld
        embedding
        (Root.literalContinuumTrace recovery selected directions localC)
        (anomalyTrace transport)) →
    (root : Root.MarkedStressOSMaxCutRoot recovery selected directions localC) →
    (positiveGravityFactor : ℚ) →
    0ℚ < positiveGravityFactor →
    0ℚ <
      Vacuum.matterAccelerationContribution
        positiveGravityFactor
        (Terminal.lorentzianIsotropicStress
          (Root.reconstructedTerminalConsequences
            recovery selected directions localC root))
  pinnedAnomalyForcesPositiveMatterAcceleration
      {embedding = embedding} {transport = transport}
      f2Weld readoutWeld root positiveGravityFactor factorPositive =
    RealToExpansion.realTraceNegativeForcesPositiveMatterAcceleration
      recovery selected directions localC
      embedding (anomalyTrace transport) readoutWeld root
      positiveGravityFactor factorPositive
      (TraceSign.pinnedLocalCStressTraceNegative f2Weld)

pinnedLocalCAnomalyRouteCompilesToMatterAcceleration : Bool
pinnedLocalCAnomalyRouteCompilesToMatterAcceleration = true

remainingAnomalyLeavesAreF2WeldReadoutWeldAndMarkedOS : Bool
remainingAnomalyLeavesAreF2WeldReadoutWeldAndMarkedOS = true
