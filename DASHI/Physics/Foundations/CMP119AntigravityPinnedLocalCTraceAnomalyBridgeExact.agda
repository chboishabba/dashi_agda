{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPinnedLocalCTraceAnomalyBridgeExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _*ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealTraceAnomalySameObjectExact as Anomaly
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

------------------------------------------------------------------------
-- SAME-CONTINUUM-FAMILY TRACE-ANOMALY READOUT
--
-- The existing local-C theorem packages:
--   * renormalized curvature-polynomial local operators;
--   * one local conserved renormalized stress tensor;
-- on one continuum family.
--
-- Their carrier types are intentionally opaque.  The anomaly lane therefore
-- needs an explicit choice of the F^2 curvature polynomial and explicit scalar
-- readouts for:
--
--   trace(T_ren),  N([F^2]_ren).
--
-- This module pins the sourced trace-anomaly authority to those exact local-C
-- objects before any finite CMP119 transport is permitted.
------------------------------------------------------------------------

record SameFamilyLocalCTraceAnomalyReadout
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set}
    (localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : SU2Trace.RealSU2TraceConvention embedding) : Set₁ where
  field
    fieldStrengthSquarePolynomial : CurvaturePolynomial

    stressTraceNumerator :
      StressTensor → ℝ

    localOperatorNumerator :
      LocalOperator → ℝ

    anomalyAuthority :
      Anomaly.RenormalizedPureYMTraceAnomalyAuthority
        embedding convention

    authorityTraceIsSelectedLocalStress :
      Anomaly.renormalizedTraceNumerator anomalyAuthority
      ≡
      stressTraceNumerator (Local.stressTensor localC)

    authorityF2IsSelectedCurvatureOperator :
      Anomaly.renormalizedF2Numerator anomalyAuthority
      ≡
      localOperatorNumerator
        (Local.localOperator localC fieldStrengthSquarePolynomial)

open SameFamilyLocalCTraceAnomalyReadout public

selectedLocalCStressTraceIsSU2BetaF2 :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian localC embedding convention}
    (readout :
      SameFamilyLocalCTraceAnomalyReadout
        {ContinuumFamily = ContinuumFamily}
        {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator}
        {Position = Position}
        {OPECoefficient = OPECoefficient}
        {StressTensor = StressTensor}
        {Hamiltonian = Hamiltonian}
        localC embedding convention) →
  stressTraceNumerator readout (Local.stressTensor localC)
  ≡
  SU2Trace.realSU2TraceCoefficient embedding convention
  *ℝ
  localOperatorNumerator readout
    (Local.localOperator localC
      (fieldStrengthSquarePolynomial readout))
selectedLocalCStressTraceIsSU2BetaF2
    {localC = localC} {embedding = embedding}
    {convention = convention} readout =
  trans
    (sym (authorityTraceIsSelectedLocalStress readout))
    (trans
      (Anomaly.renormalizedTraceIsSU2BetaF2
        (anomalyAuthority readout))
      (cong
        (λ value →
          SU2Trace.realSU2TraceCoefficient embedding convention
          *ℝ value)
        (authorityF2IsSelectedCurvatureOperator readout)))

------------------------------------------------------------------------
-- FINITE CMP119 -> SAME LOCAL-C OBJECT TRANSPORT
------------------------------------------------------------------------

record FiniteCMP119ToLocalCTraceAnomalyWeld
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian}
    {embedding : Embed.OrderedRationalRealEmbedding}
    {convention : SU2Trace.RealSU2TraceConvention embedding}
    (readout :
      SameFamilyLocalCTraceAnomalyReadout
        localC embedding convention) : Set₁ where
  field
    selectedFiniteQuantumTraceNumerator : ℝ
    selectedFiniteF2Numerator : ℝ

    finiteTraceIsLocalCStressTrace :
      selectedFiniteQuantumTraceNumerator
      ≡
      stressTraceNumerator readout (Local.stressTensor localC)

    finiteF2IsLocalCCurvatureF2 :
      selectedFiniteF2Numerator
      ≡
      localOperatorNumerator readout
        (Local.localOperator localC
          (fieldStrengthSquarePolynomial readout))

open FiniteCMP119ToLocalCTraceAnomalyWeld public

finiteCMP119TraceIsSU2BetaF2ViaPinnedLocalC :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian localC embedding convention}
    {readout :
      SameFamilyLocalCTraceAnomalyReadout
        {ContinuumFamily = ContinuumFamily}
        {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator}
        {Position = Position}
        {OPECoefficient = OPECoefficient}
        {StressTensor = StressTensor}
        {Hamiltonian = Hamiltonian}
        localC embedding convention}
    (weld : FiniteCMP119ToLocalCTraceAnomalyWeld readout) →
  selectedFiniteQuantumTraceNumerator weld
  ≡
  SU2Trace.realSU2TraceCoefficient embedding convention
  *ℝ
  selectedFiniteF2Numerator weld
finiteCMP119TraceIsSU2BetaF2ViaPinnedLocalC
    {embedding = embedding} {convention = convention}
    {readout = readout} weld =
  trans
    (finiteTraceIsLocalCStressTrace weld)
    (trans
      (selectedLocalCStressTraceIsSU2BetaF2 readout)
      (cong
        (λ value →
          SU2Trace.realSU2TraceCoefficient embedding convention
          *ℝ value)
        (sym (finiteF2IsLocalCCurvatureF2 weld))))
