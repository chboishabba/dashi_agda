{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP2HilbertTraceAnomalyExact where

------------------------------------------------------------------------
-- P2 NEW MATH: THE ANOMALY TRACE IS THE HILBERT/METRIC TRACE.
--
-- Do not introduce an independent scalar called "renormalized trace" and then
-- ask for a same-object weld to R136.  The selected continuum stress is already
-- represented by its metric pairing.  Therefore define its Hilbert trace by
-- summing the four selected diagonal metric pairings and applying the existing
-- rational->real embedding.
--
-- Round130 already identifies the literal Clay stress with the canonical metric
-- stress, and Round109/Local-C already identifies that same literal stress with
-- the pinned Local-C stress.  Consequently
--
--   embed(R136 four-diagonal response)
--     = HilbertTrace(LocalC.stressTensor)
--
-- is compiler algebra.  The genuine imported/source theorem is then stated in
-- its natural form:
--
--   HilbertTrace(T_ren) = beta/(2g) [F^2]_ren
--
-- in the repository's chosen SU(2) normalization.
--
-- This retires the old free trace-frame calibration field: the trace used by
-- the anomaly is definitionally the metric/Hilbert trace of the same stress.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)

import DASHI.Physics.Foundations.CMP119CosmologyContinuumWeylStressPairingExact as Continuum
import DASHI.Physics.Foundations.CMP119CosmologyR136LocalCSameStressExact as SameStress
import DASHI.Physics.Foundations.CMP119AntigravityPinnedLocalCTraceAnomalyBridgeExact as LocalTrace
import DASHI.Physics.Foundations.CMP119AntigravityRealTraceAnomalySameObjectExact as Anomaly
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
import DASHI.Physics.YangMills.BalabanCanonicalMetricToCMP119StressRound118Exact as R118
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanContinuumMetricStressPairingRound130Exact as R130
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
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
  where

  domain = R134.presentCutCanonicalMetricDomain metricInputs
  metricWeld = R136.metricPairing recovery
  localPackage = ConcreteLocalC.compileConcretePinnedLocalPackage concreteLocalC

  rationalReadout : StressRep.PairingScalar representation → ℚ
  rationalReadout =
    R118.readoutToRational (R119.asRound118CanonicalMetricWeld selected)

  representedHilbertTrace : Top.StressTensor C → ℚ
  representedHilbertTrace stress =
    let represented = R130.literalStressToRepresentation metricWeld stress
    in
    (rationalReadout
        (StressRep.stressMetricPairing representation represented
          (Continuum.h00 directions))
      + rationalReadout
        (StressRep.stressMetricPairing representation represented
          (Continuum.h11 directions)))
    +
    (rationalReadout
        (StressRep.stressMetricPairing representation represented
          (Continuum.h22 directions))
      + rationalReadout
        (StressRep.stressMetricPairing representation represented
          (Continuum.h33 directions)))

  hilbertTraceNumerator : Top.StressTensor C → ℝ
  hilbertTraceNumerator stress =
    Embed.embed embedding (representedHilbertTrace stress)

  localCHilbertTraceIsLiteralStressPairing :
    representedHilbertTrace (ConcreteLocalC.stressTensor concreteLocalC)
    ≡ Continuum.literalStressFourDiagonalPairing recovery selected directions
  localCHilbertTraceIsLiteralStressPairing =
    cong
      (λ represented →
        (rationalReadout
            (StressRep.stressMetricPairing representation represented
              (Continuum.h00 directions))
          + rationalReadout
            (StressRep.stressMetricPairing representation represented
              (Continuum.h11 directions)))
        +
        (rationalReadout
            (StressRep.stressMetricPairing representation represented
              (Continuum.h22 directions))
          + rationalReadout
            (StressRep.stressMetricPairing representation represented
              (Continuum.h33 directions))))
      (SameStress.representedLocalCStressIsCanonicalStress
        Y group metricWeld concreteLocalC round109)

  embeddedR136IsPinnedLocalCHilbertTrace :
    Embed.embed embedding
      (Continuum.continuumFourDiagonalResponse recovery selected directions)
    ≡ hilbertTraceNumerator (ConcreteLocalC.stressTensor concreteLocalC)
  embeddedR136IsPinnedLocalCHilbertTrace =
    trans
      (cong (Embed.embed embedding)
        (Continuum.continuumFourDiagonalResponseIsLiteralStressPairing
          recovery selected directions))
      (cong (Embed.embed embedding)
        (sym localCHilbertTraceIsLiteralStressPairing))

  record HilbertTraceAnomalySource : Set₁ where
    field
      fieldStrengthSquarePolynomial : CurvaturePolynomial
      localOperatorNumerator : LocalOperator → ℝ

      -- This is the source theorem in its natural object language.  There is no
      -- independently selected trace scalar: the left side is the Hilbert trace
      -- of the exact pinned Local-C/R136 stress.
      hilbertTraceIsSU2BetaF2 :
        hilbertTraceNumerator (ConcreteLocalC.stressTensor concreteLocalC)
        ≡
        SU2Trace.realSU2TraceCoefficient embedding convention
        *ℝ
        localOperatorNumerator
          (Local.localOperator localPackage fieldStrengthSquarePolynomial)

  open HilbertTraceAnomalySource public

  asSameFamilyLocalCTraceAnomalyReadout :
    HilbertTraceAnomalySource →
    LocalTrace.SameFamilyLocalCTraceAnomalyReadout
      localPackage embedding convention
  asSameFamilyLocalCTraceAnomalyReadout source =
    let
      authority : Anomaly.RenormalizedPureYMTraceAnomalyAuthority embedding convention
      authority = record
        { Anomaly.RenormalizedPureYMTraceAnomalyAuthority.renormalizedF2Numerator =
            localOperatorNumerator source
              (Local.localOperator localPackage
                (fieldStrengthSquarePolynomial source))
        ; Anomaly.RenormalizedPureYMTraceAnomalyAuthority.renormalizedTraceNumerator =
            hilbertTraceNumerator (ConcreteLocalC.stressTensor concreteLocalC)
        ; Anomaly.RenormalizedPureYMTraceAnomalyAuthority.renormalizedTraceIsSU2BetaF2 =
            hilbertTraceIsSU2BetaF2 source
        }
    in record
      { LocalTrace.SameFamilyLocalCTraceAnomalyReadout.fieldStrengthSquarePolynomial =
          fieldStrengthSquarePolynomial source
      ; LocalTrace.SameFamilyLocalCTraceAnomalyReadout.stressTraceNumerator =
          hilbertTraceNumerator
      ; LocalTrace.SameFamilyLocalCTraceAnomalyReadout.localOperatorNumerator =
          localOperatorNumerator source
      ; LocalTrace.SameFamilyLocalCTraceAnomalyReadout.anomalyAuthority =
          authority
      ; LocalTrace.SameFamilyLocalCTraceAnomalyReadout.authorityTraceIsSelectedLocalStress =
          refl
      ; LocalTrace.SameFamilyLocalCTraceAnomalyReadout.authorityF2IsSelectedCurvatureOperator =
          refl
      }

  freeTraceFrameCalibrationNoLongerRequired : Bool
  freeTraceFrameCalibrationNoLongerRequired = true

  p2IsDefinitionOfHilbertTracePlusSourceTraceAnomaly : Bool
  p2IsDefinitionOfHilbertTracePlusSourceTraceAnomaly = true
