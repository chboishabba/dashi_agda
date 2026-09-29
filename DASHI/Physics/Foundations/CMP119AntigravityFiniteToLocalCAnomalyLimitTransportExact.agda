{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityFiniteToLocalCAnomalyLimitTransportExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; absℝ; _-ℝ_; _≤ℝ_; _<ℝ_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119AntigravityPinnedLocalCTraceAnomalyBridgeExact as LocalCBridge
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

------------------------------------------------------------------------
-- CORRECT FINITE -> CONTINUUM ANOMALY TRANSPORT
--
-- A finite-cutoff CMP119 numerator is not definitionally equal to a
-- renormalized continuum Local-C readout.  The physically correct same-family
-- statement is convergence with a controlled renormalization/continuum error:
--
--   |T_ren - T_n| <= eps_T(n),    eps_T -> 0
--   |F2_ren - F2_n| <= eps_F(n),  eps_F -> 0.
--
-- The repository's real-sequence limit authority then identifies the limits
-- with the exact pinned Local-C stress-trace and F^2 readouts.
------------------------------------------------------------------------

record FiniteCMP119ToLocalCAnomalyLimitTransport
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian}
    {embedding : Embed.OrderedRationalRealEmbedding}
    {convention : SU2Trace.RealSU2TraceConvention embedding}
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError)
    (readout :
      LocalCBridge.SameFamilyLocalCTraceAnomalyReadout
        localC embedding convention) : Set₁ where
  field
    finiteQuantumTraceNumerator : Nat → ℝ
    finiteF2Numerator : Nat → ℝ

    traceError : Nat → ℝ
    f2Error : Nat → ℝ

    finiteTraceApproximatesLocalC :
      ∀ cutoff →
      absℝ
        (LocalCBridge.stressTraceNumerator readout
          (Local.stressTensor localC)
          -ℝ finiteQuantumTraceNumerator cutoff)
      ≤ℝ traceError cutoff

    finiteF2ApproximatesLocalC :
      ∀ cutoff →
      absℝ
        (LocalCBridge.localOperatorNumerator readout
          (Local.localOperator localC
            (LocalCBridge.fieldStrengthSquarePolynomial readout))
          -ℝ finiteF2Numerator cutoff)
      ≤ℝ f2Error cutoff

    traceErrorVanishes :
      Seq.Vanishes sequenceLimit traceError

    f2ErrorVanishes :
      Seq.Vanishes sequenceLimit f2Error

open FiniteCMP119ToLocalCAnomalyLimitTransport public

finiteTraceLimitIsPinnedLocalCTrace :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian localC embedding convention}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {readout :
      LocalCBridge.SameFamilyLocalCTraceAnomalyReadout
        {ContinuumFamily = ContinuumFamily}
        {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator}
        {Position = Position}
        {OPECoefficient = OPECoefficient}
        {StressTensor = StressTensor}
        {Hamiltonian = Hamiltonian}
        localC embedding convention}
    (transport :
      FiniteCMP119ToLocalCAnomalyLimitTransport
        sequenceLimit readout) →
  Seq.limit sequenceLimit (finiteQuantumTraceNumerator transport)
  ≡
  LocalCBridge.stressTraceNumerator readout
    (Local.stressTensor localC)
finiteTraceLimitIsPinnedLocalCTrace
    {localC = localC} {sequenceLimit = sequenceLimit} {readout = readout}
    transport =
  Seq.limitFromVanishingError sequenceLimit
    (finiteQuantumTraceNumerator transport)
    (LocalCBridge.stressTraceNumerator readout
      (Local.stressTensor localC))
    (traceError transport)
    (finiteTraceApproximatesLocalC transport)
    (traceErrorVanishes transport)

finiteF2LimitIsPinnedLocalCF2 :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian localC embedding convention}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {readout :
      LocalCBridge.SameFamilyLocalCTraceAnomalyReadout
        {ContinuumFamily = ContinuumFamily}
        {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator}
        {Position = Position}
        {OPECoefficient = OPECoefficient}
        {StressTensor = StressTensor}
        {Hamiltonian = Hamiltonian}
        localC embedding convention}
    (transport :
      FiniteCMP119ToLocalCAnomalyLimitTransport
        sequenceLimit readout) →
  Seq.limit sequenceLimit (finiteF2Numerator transport)
  ≡
  LocalCBridge.localOperatorNumerator readout
    (Local.localOperator localC
      (LocalCBridge.fieldStrengthSquarePolynomial readout))
finiteF2LimitIsPinnedLocalCF2
    {localC = localC} {sequenceLimit = sequenceLimit} {readout = readout}
    transport =
  Seq.limitFromVanishingError sequenceLimit
    (finiteF2Numerator transport)
    (LocalCBridge.localOperatorNumerator readout
      (Local.localOperator localC
        (LocalCBridge.fieldStrengthSquarePolynomial readout)))
    (f2Error transport)
    (finiteF2ApproximatesLocalC transport)
    (f2ErrorVanishes transport)

finiteEqualsContinuumAnomalyReadoutRequired : Bool
finiteEqualsContinuumAnomalyReadoutRequired = false

finiteEqualsContinuumAnomalyReadoutRequiredIsFalse :
  finiteEqualsContinuumAnomalyReadoutRequired ≡ false
finiteEqualsContinuumAnomalyReadoutRequiredIsFalse = refl

finiteToContinuumVanishingErrorTransportRequired : Bool
finiteToContinuumVanishingErrorTransportRequired = true

finiteToContinuumVanishingErrorTransportRequiredIsTrue :
  finiteToContinuumVanishingErrorTransportRequired ≡ true
finiteToContinuumVanishingErrorTransportRequiredIsTrue = refl

finiteToLocalCAnomalyLimitTransportCompilerLevel : ProofLevel
finiteToLocalCAnomalyLimitTransportCompilerLevel = machineChecked
