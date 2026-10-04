{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR136TraceFrameCalibrationExact where

------------------------------------------------------------------------
-- R136 ANOMALY MAX-CUT: THE REMAINING WELD IS A TRACE-FRAME CALIBRATION.
--
-- R136 already pairs the literal Clay stress with four admitted metric
-- perturbations.  Round109/Local-C already says that literal Clay stress is the
-- selected concrete Local-C stress.  Therefore the anomaly route does NOT need
-- another stress object.
--
-- What is not present in `FourAdmittedMetricDirections` is the geometric/readout
-- theorem saying that the chosen four perturbations and rational readout really
-- compute the renormalized diagonal trace used by the Local-C anomaly theorem.
-- Keep exactly that scalar calibration explicit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyR136LocalCTraceAnomalyExact as Direct
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as RealBridge
import DASHI.Physics.Foundations.CMP119AntigravityPinnedLocalCTraceAnomalyBridgeExact as LocalTrace
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
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as ConcreteLocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119Round109ConcreteLocalCExact as Round109

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
      (R134.presentCutCanonicalMetricDomain metricInputs) representation coordinate)
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
    (readout :
      LocalTrace.SameFamilyLocalCTraceAnomalyReadout
        (ConcreteLocalC.compileConcretePinnedLocalPackage concreteLocalC)
        embedding convention)
  where

  r136Response = Continuum.continuumFourDiagonalResponse recovery selected directions

  localCTrace : ℝ
  localCTrace =
    LocalTrace.stressTraceNumerator readout
      (ConcreteLocalC.stressTensor concreteLocalC)

  record TraceFrameCalibration : Set₁ where
    field
      embeddedFourDirectionPairingIsLiteralClayStressTrace :
        Embed.embed embedding
          (Continuum.literalStressFourDiagonalPairing recovery selected directions)
        ≡ LocalTrace.stressTraceNumerator readout (Top.stressTensor Y group)

  open TraceFrameCalibration public

  embeddedR136IsLocalCTrace :
    TraceFrameCalibration →
    Embed.embed embedding r136Response ≡ localCTrace
  embeddedR136IsLocalCTrace calibration =
    trans
      (cong (Embed.embed embedding)
        (Continuum.continuumFourDiagonalResponseIsLiteralStressPairing
          recovery selected directions))
      (trans
        (embeddedFourDirectionPairingIsLiteralClayStressTrace calibration)
        (cong (LocalTrace.stressTraceNumerator readout)
          (Round109.literalClayStressIsConcreteLocalCStress round109)))

  asDirectLocalCTraceWeld :
    TraceFrameCalibration →
    Direct.R136LocalCTraceReadoutWeld readout r136Response
  asDirectLocalCTraceWeld calibration = record
    { Direct.R136LocalCTraceReadoutWeld.embeddedR136IsSelectedLocalCStressTrace =
        embeddedR136IsLocalCTrace calibration
    }

  asRealTraceReadoutWeld :
    TraceFrameCalibration →
    RealBridge.NegativeOrderReflectionAtZero embedding →
    RealBridge.R136RealTraceReadoutWeld embedding r136Response localCTrace
  asRealTraceReadoutWeld calibration reflection = record
    { RealBridge.R136RealTraceReadoutWeld.sameReadout =
        embeddedR136IsLocalCTrace calibration
    ; RealBridge.R136RealTraceReadoutWeld.negativeReflection = reflection
    }

fourAdmittedDirectionsDoNotByThemselvesDefineRenormalizedTrace : Bool
fourAdmittedDirectionsDoNotByThemselvesDefineRenormalizedTrace = true

remainingAnomalyWeldIsScalarTraceFrameCalibration : Bool
remainingAnomalyWeldIsScalarTraceFrameCalibration = true

noSecondStressObjectNeededForAnomalyRoute : Bool
noSecondStressObjectNeededForAnomalyRoute = true

traceFrameCalibrationCompilesToExistingRealTraceBridge : Bool
traceFrameCalibrationCompilesToExistingRealTraceBridge = true
