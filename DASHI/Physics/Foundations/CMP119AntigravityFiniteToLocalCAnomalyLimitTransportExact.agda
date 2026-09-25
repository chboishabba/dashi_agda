{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityFiniteToLocalCAnomalyLimitTransportExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; absℝ; _-ℝ_; _≤ℝ_; _<ℝ_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119AntigravityPinnedLocalCTraceAnomalyBridgeExact as LocalC
import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

------------------------------------------------------------------------
-- CORRECT FINITE -> CONTINUUM ANOMALY TRANSPORT
--
-- A finite-cutoff CMP119 numerator is not definitionally equal to a
-- renormalized continuum Local-C readout.  The physically correct same-family
-- statement is convergence with a controlled renormalization/continuum error.
--
-- This module therefore replaces exact finite=continuum equality by:
--
--   |T_ren - T_n| <= eps_T(n),    eps_T -> 0
--   |F2_ren - F2_n| <= eps_F(n),  eps_F -> 0.
--
-- The repository's standard real-sequence limit authority then proves that
-- both finite sequences have the selected Local-C readouts as their limits.
------------------------------------------------------------------------

record FiniteCMP119ToLocalCAnomalyLimitTransport
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set}
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError)
    (readout :
      LocalC.SameFamilyLocalCTraceAnomalyReadout
        {ContinuumFamily = ContinuumFamily}
        {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator}
        {Position = Position}
        {OPECoefficient = OPECoefficient}
        {StressTensor = StressTensor}
        {Hamiltonian = Hamiltonian}
        _ _ _) : Set₁ where
  field
    finiteQuantumTraceNumerator : Nat → ℝ
    finiteF2Numerator : Nat → ℝ

    traceError : Nat → ℝ
    f2Error : Nat → ℝ

    finiteTraceApproximatesLocalC :
      ∀ cutoff →
      absℝ
        (LocalC.stressTraceNumerator readout
          (DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact.stressTensor _)
          -ℝ finiteQuantumTraceNumerator cutoff)
      ≤ℝ traceError cutoff

    finiteF2ApproximatesLocalC :
      ∀ cutoff →
      absℝ
        (LocalC.localOperatorNumerator readout
          (DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact.localOperator _
            (LocalC.fieldStrengthSquarePolynomial readout))
          -ℝ finiteF2Numerator cutoff)
      ≤ℝ f2Error cutoff

    traceErrorVanishes :
      Seq.Vanishes sequenceLimit traceError

    f2ErrorVanishes :
      Seq.Vanishes sequenceLimit f2Error

open FiniteCMP119ToLocalCAnomalyLimitTransport public
