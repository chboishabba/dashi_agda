{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR136LocalCTraceAnomalyExact where

------------------------------------------------------------------------
-- DIRECT R136 -> LOCAL-C TRACE-ANOMALY SIGN COMPILER.
--
-- Do not introduce an independently selected "quantum trace" scalar.  The
-- pinned Local-C anomaly readout already evaluates the SAME renormalized Local-C
-- stress tensor and proves
--
--   trace(T_LocalC) = b_YM * [F^2]_LocalC.
--
-- Hence R136 negativity needs only:
--   1. the scalar convention identifying embedded R136 four-direction pairing
--      with that Local-C stress trace readout;
--   2. strict positivity of the selected Local-C F^2 numerator.
--
-- The SU(2) beta/trace coefficient negativity and the trace identity are
-- already compiler/source-authority outputs.  Eq.(2.23) vacuum-sector metric
-- signs are not consumed on this route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _<ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityPinnedLocalCTraceAnomalyBridgeExact as LocalTrace
import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local

record R136LocalCTraceReadoutWeld
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian}
    {embedding : Embed.OrderedRationalRealEmbedding}
    {convention : SU2Trace.RealSU2TraceConvention embedding}
    (readout :
      LocalTrace.SameFamilyLocalCTraceAnomalyReadout
        localC embedding convention)
    (r136Response : ℚ) : Set₁ where
  field
    embeddedR136IsSelectedLocalCStressTrace :
      Embed.embed embedding r136Response
      ≡
      LocalTrace.stressTraceNumerator readout (Local.stressTensor localC)

open R136LocalCTraceReadoutWeld public

embeddedR136NegativeFromLocalCTraceAnomaly :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian localC embedding convention}
    (strict : Strict.RealStrictSignLaws)
    (readout :
      LocalTrace.SameFamilyLocalCTraceAnomalyReadout
        {ContinuumFamily = ContinuumFamily}
        {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator}
        {Position = Position}
        {OPECoefficient = OPECoefficient}
        {StressTensor = StressTensor}
        {Hamiltonian = Hamiltonian}
        localC embedding convention)
    (r136Response : ℚ)
    (weld : R136LocalCTraceReadoutWeld readout r136Response) →
  0ℝ <ℝ
    LocalTrace.localOperatorNumerator readout
      (Local.localOperator localC
        (LocalTrace.fieldStrengthSquarePolynomial readout)) →
  Embed.embed embedding r136Response <ℝ 0ℝ
embeddedR136NegativeFromLocalCTraceAnomaly
    {localC = localC} {embedding = embedding} {convention = convention}
    strict readout r136Response weld f2Positive =
  let
    localTraceNegative :
      LocalTrace.stressTraceNumerator readout (Local.stressTensor localC)
      <ℝ 0ℝ
    localTraceNegative =
      subst
        (λ value → value <ℝ 0ℝ)
        (sym (LocalTrace.selectedLocalCStressTraceIsSU2BetaF2 readout))
        (Strict.negativeTimesPositive strict
          (SU2Trace.realSU2TraceCoefficientNegative
            strict embedding convention)
          f2Positive)
  in
  subst
    (λ value → value <ℝ 0ℝ)
    (sym (embeddedR136IsSelectedLocalCStressTrace weld))
    localTraceNegative

noSeparateSelectedQuantumTraceCarrier : Bool
noSeparateSelectedQuantumTraceCarrier = true

eq223VacuumGapNotNeededOnDirectLocalCAnomalyRoute : Bool
eq223VacuumGapNotNeededOnDirectLocalCAnomalyRoute = true

remainingSignPhysicsIsSameStressTraceReadoutAndLocalCF2Positivity : Bool
remainingSignPhysicsIsSameStressTraceReadoutAndLocalCF2Positivity = true
