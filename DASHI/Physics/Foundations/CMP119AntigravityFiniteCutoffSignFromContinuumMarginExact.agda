{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityFiniteCutoffSignFromContinuumMarginExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; absℝ; _-ℝ_; _≤ℝ_; _<ℝ_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119AntigravityFiniteToLocalCAnomalyLimitTransportExact as LimitTransport
import DASHI.Physics.Foundations.CMP119AntigravityPinnedLocalCTraceAnomalyBridgeExact as LocalCBridge
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

------------------------------------------------------------------------
-- STANDARD REAL SIGN-STABILITY AUTHORITY
--
-- The repo's minimal real authority surface does not expose the elementary
-- theorem that an approximation closer than the distance to zero preserves a
-- strict sign.  Keep that ordinary real-analysis fact explicit and generic.
------------------------------------------------------------------------

record RealApproximationSignStability : Set₁ where
  field
    negativeStable :
      ∀ target approximate error →
      target <ℝ 0ℝ →
      absℝ (target -ℝ approximate) ≤ℝ error →
      error <ℝ absℝ target →
      approximate <ℝ 0ℝ

    positiveStable :
      ∀ target approximate error →
      0ℝ <ℝ target →
      absℝ (target -ℝ approximate) ≤ℝ error →
      error <ℝ absℝ target →
      0ℝ <ℝ approximate

open RealApproximationSignStability public

realApproximationSignStabilityLevel : ProofLevel
realApproximationSignStabilityLevel = standardImported

------------------------------------------------------------------------
-- SELECTED CUTOFF SIGN TRANSPORT
------------------------------------------------------------------------

record SelectedCutoffAnomalyErrorMargin
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian}
    {embedding : Embed.OrderedRationalRealEmbedding}
    {convention : SU2Trace.RealSU2TraceConvention embedding}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {readout :
      LocalCBridge.SameFamilyLocalCTraceAnomalyReadout
        localC embedding convention}
    (transport :
      LimitTransport.FiniteCMP119ToLocalCAnomalyLimitTransport
        sequenceLimit readout)
    (cutoff : Nat) : Set₁ where
  field
    continuumTraceNegative :
      LocalCBridge.stressTraceNumerator readout
        (Local.stressTensor localC)
      <ℝ 0ℝ

    continuumF2Positive :
      0ℝ
      <ℝ
      LocalCBridge.localOperatorNumerator readout
        (Local.localOperator localC
          (LocalCBridge.fieldStrengthSquarePolynomial readout))

    traceErrorInsideSignMargin :
      LimitTransport.traceError transport cutoff
      <ℝ
      absℝ
        (LocalCBridge.stressTraceNumerator readout
          (Local.stressTensor localC))

    f2ErrorInsideSignMargin :
      LimitTransport.f2Error transport cutoff
      <ℝ
      absℝ
        (LocalCBridge.localOperatorNumerator readout
          (Local.localOperator localC
            (LocalCBridge.fieldStrengthSquarePolynomial readout)))

open SelectedCutoffAnomalyErrorMargin public

finiteTraceNegativeAtSelectedCutoff :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian localC embedding convention
      sequenceLimit readout}
    (stability : RealApproximationSignStability)
    (transport :
      LimitTransport.FiniteCMP119ToLocalCAnomalyLimitTransport
        {ContinuumFamily = ContinuumFamily}
        {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator}
        {Position = Position}
        {OPECoefficient = OPECoefficient}
        {StressTensor = StressTensor}
        {Hamiltonian = Hamiltonian}
        {localC = localC}
        {embedding = embedding}
        {convention = convention}
        sequenceLimit readout)
    (cutoff : Nat)
    (margin : SelectedCutoffAnomalyErrorMargin transport cutoff) →
  LimitTransport.finiteQuantumTraceNumerator transport cutoff <ℝ 0ℝ
finiteTraceNegativeAtSelectedCutoff
    {localC = localC} {readout = readout}
    stability transport cutoff margin =
  negativeStable stability
    (LocalCBridge.stressTraceNumerator readout
      (Local.stressTensor localC))
    (LimitTransport.finiteQuantumTraceNumerator transport cutoff)
    (LimitTransport.traceError transport cutoff)
    (continuumTraceNegative margin)
    (LimitTransport.finiteTraceApproximatesLocalC transport cutoff)
    (traceErrorInsideSignMargin margin)

finiteF2PositiveAtSelectedCutoff :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian localC embedding convention
      sequenceLimit readout}
    (stability : RealApproximationSignStability)
    (transport :
      LimitTransport.FiniteCMP119ToLocalCAnomalyLimitTransport
        {ContinuumFamily = ContinuumFamily}
        {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator}
        {Position = Position}
        {OPECoefficient = OPECoefficient}
        {StressTensor = StressTensor}
        {Hamiltonian = Hamiltonian}
        {localC = localC}
        {embedding = embedding}
        {convention = convention}
        sequenceLimit readout)
    (cutoff : Nat)
    (margin : SelectedCutoffAnomalyErrorMargin transport cutoff) →
  0ℝ <ℝ LimitTransport.finiteF2Numerator transport cutoff
finiteF2PositiveAtSelectedCutoff
    {localC = localC} {readout = readout}
    stability transport cutoff margin =
  positiveStable stability
    (LocalCBridge.localOperatorNumerator readout
      (Local.localOperator localC
        (LocalCBridge.fieldStrengthSquarePolynomial readout)))
    (LimitTransport.finiteF2Numerator transport cutoff)
    (LimitTransport.f2Error transport cutoff)
    (continuumF2Positive margin)
    (LimitTransport.finiteF2ApproximatesLocalC transport cutoff)
    (f2ErrorInsideSignMargin margin)

finiteCutoffSignTransportCompilerLevel : ProofLevel
finiteCutoffSignTransportCompilerLevel = machineChecked
