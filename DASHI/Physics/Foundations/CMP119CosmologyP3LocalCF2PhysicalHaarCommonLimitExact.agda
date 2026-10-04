{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3LocalCF2PhysicalHaarCommonLimitExact where

------------------------------------------------------------------------
-- P3 NEW MATH: LOCAL-C F^2 AND PHYSICAL HAAR F^2 ARE ONE COMMON LIMIT.
--
-- A renormalized continuum F^2 readout should NOT be identified exactly with
-- one finite-cutoff Wilson/Gibbs numerator.  The branch already has the correct
-- ingredients:
--
--   (1) finite CMP119 F^2_n -> pinned Local-C F^2 with a vanishing error;
--   (2) finite CMP119 F^2_n -> physical Haar F^2 with a vanishing error.
--
-- If these are pointwise the SAME finite sequence, the canonical limit's
-- congruence law gives
--
--       LocalC(F^2) = physicalHaar(F^2).
--
-- No function extensionality and no exact finite=continuum identity is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _<ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityFiniteToLocalCAnomalyLimitTransportExact as LocalLimit
import DASHI.Physics.Foundations.CMP119AntigravityRealHaarExpectationRepresentationExact as HaarLimit
import DASHI.Physics.Foundations.CMP119AntigravityPinnedLocalCTraceAnomalyBridgeExact as LocalTrace
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

record LocalCF2PhysicalHaarCommonLimit
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian}
    {embedding : Embed.OrderedRationalRealEmbedding}
    {convention : SU2Trace.RealSU2TraceConvention embedding}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (readout :
      LocalTrace.SameFamilyLocalCTraceAnomalyReadout
        localC embedding convention)
    (localTransport :
      LocalLimit.FiniteCMP119ToLocalCAnomalyLimitTransport
        sequenceLimit readout)
    (physicalHaar :
      HaarLimit.RealHaarExpectationRepresentation sequenceLimit)
    : Set₁ where
  field
    sameFiniteF2Sequence :
      ∀ cutoff →
      LocalLimit.finiteF2Numerator localTransport cutoff
      ≡ HaarLimit.finiteCMP119Expectation physicalHaar cutoff

open LocalCF2PhysicalHaarCommonLimit public

localCF2EqualsPhysicalHaarExpectation :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian localC embedding convention
      sequenceLimit readout localTransport physicalHaar} →
  LocalCF2PhysicalHaarCommonLimit
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
    {sequenceLimit = sequenceLimit}
    readout localTransport physicalHaar →
  LocalTrace.localOperatorNumerator readout
    (Local.localOperator localC
      (LocalTrace.fieldStrengthSquarePolynomial readout))
  ≡ HaarLimit.physicalHaarExpectation physicalHaar
localCF2EqualsPhysicalHaarExpectation
    {sequenceLimit = sequenceLimit}
    {readout = readout}
    {localTransport = localTransport}
    {physicalHaar = physicalHaar}
    common =
  trans
    (sym
      (LocalLimit.finiteF2LimitIsPinnedLocalCF2 localTransport))
    (trans
      (Seq.limitCongruent sequenceLimit
        (LocalLimit.finiteF2Numerator localTransport)
        (HaarLimit.finiteCMP119Expectation physicalHaar)
        (sameFiniteF2Sequence common))
      (HaarLimit.physicalHaarExpectationIsFiniteCMP119Limit physicalHaar))

physicalHaarPositiveGivesLocalCF2Positive :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian localC embedding convention
      sequenceLimit readout localTransport physicalHaar}
    (common :
      LocalCF2PhysicalHaarCommonLimit
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
        {sequenceLimit = sequenceLimit}
        readout localTransport physicalHaar) →
  0ℝ <ℝ HaarLimit.physicalHaarExpectation physicalHaar →
  0ℝ <ℝ
    LocalTrace.localOperatorNumerator readout
      (Local.localOperator localC
        (LocalTrace.fieldStrengthSquarePolynomial readout))
physicalHaarPositiveGivesLocalCF2Positive common physicalPositive =
  subst
    (λ value → 0ℝ <ℝ value)
    (sym (localCF2EqualsPhysicalHaarExpectation common))
    physicalPositive

exactFiniteEqualsContinuumF2NoLongerRequired : Bool
exactFiniteEqualsContinuumF2NoLongerRequired = true

functionExtensionalityNotRequiredForCommonLimit : Bool
functionExtensionalityNotRequiredForCommonLimit = true

p3ReducesToPointwiseSameFiniteSequenceAndTwoExistingLimitRepresentations : Bool
p3ReducesToPointwiseSameFiniteSequenceAndTwoExistingLimitRepresentations = true

p3CommonLimitIsOrdinaryAnalysisNotNewAnomalyPhysics : Bool
p3CommonLimitIsOrdinaryAnalysisNotNewAnomalyPhysics = true
