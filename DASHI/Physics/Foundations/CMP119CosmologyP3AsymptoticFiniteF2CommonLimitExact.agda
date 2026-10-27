{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3AsymptoticFiniteF2CommonLimitExact where

------------------------------------------------------------------------
-- P3 MAX-CUT: ASYMPTOTIC COMMON FINITE F^2, NOT TERMWISE EQUALITY
--
-- The older P3 common-limit bridge asked the Local-C and physical-Haar routes
-- to expose literally the same finite F^2 sequence.  That is stronger than the
-- analysis requires.  It is enough that their finite sequences differ by a
-- vanishing error:
--
--   |F2_Haar(n) - F2_LocalC(n)| <= eps_bridge(n),   eps_bridge -> 0.
--
-- The physical-Haar representation already gives
--
--   |F2_Haar - F2_Haar(n)| <= eps_Haar(n),         eps_Haar -> 0,
--
-- so triangle inequality gives a vanishing majorant for the Local-C finite
-- sequence against the SAME physical-Haar target.  The existing sequence-limit
-- authority then identifies that target with the Local-C continuum readout.
--
-- This strictly weakens Q3.  No exact finite=continuum equality and no
-- pointwise equality of the two finite sequences is required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _-ℝ_; absℝ; _≤ℝ_;
   ≤ℝ-refl; ≤ℝ-trans; +-mono-≤; absZero; absAddSubadditive;
   subSelf; subAddCancelMiddle)

import DASHI.Physics.Foundations.CMP119AntigravityFiniteToLocalCAnomalyLimitTransportExact as LocalLimit
import DASHI.Physics.Foundations.CMP119AntigravityRealHaarExpectationRepresentationExact as HaarLimit
import DASHI.Physics.Foundations.CMP119AntigravityPinnedLocalCTraceAnomalyBridgeExact as LocalTrace
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanRealVanishingFiniteAlgebraExact as Vanishing

record AsymptoticCommonFiniteF2
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
      LocalTrace.SameFamilyLocalCTraceAnomalyReadout
        localC embedding convention}
    (localTransport :
      LocalLimit.FiniteCMP119ToLocalCAnomalyLimitTransport
        sequenceLimit readout)
    (physicalHaar :
      HaarLimit.RealHaarExpectationRepresentation sequenceLimit) : Set₁ where
  field
    bridgeError : Nat → ℝ

    finiteF2BridgeBound :
      ∀ cutoff →
      absℝ
        (HaarLimit.finiteCMP119Expectation physicalHaar cutoff
          -ℝ LocalLimit.finiteF2Numerator localTransport cutoff)
      ≤ℝ bridgeError cutoff

    bridgeErrorVanishes :
      Seq.Vanishes sequenceLimit bridgeError

open AsymptoticCommonFiniteF2 public

localFiniteF2ApproximatesPhysicalHaar :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian localC embedding convention
      sequenceLimit readout localTransport physicalHaar}
    (common :
      AsymptoticCommonFiniteF2
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
        {readout = readout}
        localTransport physicalHaar) →
  ∀ cutoff →
  absℝ
    (HaarLimit.physicalHaarExpectation physicalHaar
      -ℝ LocalLimit.finiteF2Numerator localTransport cutoff)
  ≤ℝ
  HaarLimit.representationError physicalHaar cutoff
    +ℝ bridgeError common cutoff
localFiniteF2ApproximatesPhysicalHaar
    {localTransport = localTransport}
    {physicalHaar = physicalHaar}
    common cutoff =
  let
    physical = HaarLimit.physicalHaarExpectation physicalHaar
    haarFinite = HaarLimit.finiteCMP119Expectation physicalHaar cutoff
    localFinite = LocalLimit.finiteF2Numerator localTransport cutoff

    triangle :
      absℝ
        ((physical -ℝ haarFinite) +ℝ (haarFinite -ℝ localFinite))
      ≤ℝ
      absℝ (physical -ℝ haarFinite)
        +ℝ absℝ (haarFinite -ℝ localFinite)
    triangle =
      absAddSubadditive
        (physical -ℝ haarFinite)
        (haarFinite -ℝ localFinite)

    bounded :
      absℝ (physical -ℝ haarFinite)
        +ℝ absℝ (haarFinite -ℝ localFinite)
      ≤ℝ
      HaarLimit.representationError physicalHaar cutoff
        +ℝ bridgeError common cutoff
    bounded =
      +-mono-≤
        (HaarLimit.finiteApproximatesPhysical physicalHaar cutoff)
        (finiteF2BridgeBound common cutoff)
  in
  subst
    (λ difference →
      absℝ difference
      ≤ℝ
      HaarLimit.representationError physicalHaar cutoff
        +ℝ bridgeError common cutoff)
    (subAddCancelMiddle physical haarFinite localFinite)
    (≤ℝ-trans triangle bounded)

combinedPhysicalBridgeErrorVanishes :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian localC embedding convention
      sequenceLimit readout localTransport physicalHaar}
    (vanishing : Vanishing.RealVanishingFiniteAlgebra sequenceLimit)
    (common :
      AsymptoticCommonFiniteF2
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
        {readout = readout}
        localTransport physicalHaar) →
  Seq.Vanishes sequenceLimit
    (λ cutoff →
      HaarLimit.representationError physicalHaar cutoff
        +ℝ bridgeError common cutoff)
combinedPhysicalBridgeErrorVanishes
    {physicalHaar = physicalHaar}
    vanishing common =
  Vanishing.vanishesAdd vanishing
    (HaarLimit.representationError physicalHaar)
    (bridgeError common)
    (HaarLimit.representationErrorVanishes physicalHaar)
    (bridgeErrorVanishes common)

localFiniteF2LimitIsPhysicalHaar :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian localC embedding convention
      sequenceLimit readout localTransport physicalHaar}
    (vanishing : Vanishing.RealVanishingFiniteAlgebra sequenceLimit)
    (common :
      AsymptoticCommonFiniteF2
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
        {readout = readout}
        localTransport physicalHaar) →
  Seq.limit sequenceLimit (LocalLimit.finiteF2Numerator localTransport)
  ≡ HaarLimit.physicalHaarExpectation physicalHaar
localFiniteF2LimitIsPhysicalHaar
    {sequenceLimit = sequenceLimit}
    {localTransport = localTransport}
    {physicalHaar = physicalHaar}
    vanishing common =
  Seq.limitFromVanishingError sequenceLimit
    (LocalLimit.finiteF2Numerator localTransport)
    (HaarLimit.physicalHaarExpectation physicalHaar)
    (λ cutoff →
      HaarLimit.representationError physicalHaar cutoff
        +ℝ bridgeError common cutoff)
    (localFiniteF2ApproximatesPhysicalHaar common)
    (combinedPhysicalBridgeErrorVanishes vanishing common)

localCF2EqualsPhysicalHaarFromAsymptoticBridge :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian localC embedding convention
      sequenceLimit readout localTransport physicalHaar}
    (vanishing : Vanishing.RealVanishingFiniteAlgebra sequenceLimit)
    (common :
      AsymptoticCommonFiniteF2
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
        {readout = readout}
        localTransport physicalHaar) →
  LocalTrace.localOperatorNumerator readout
    (Local.localOperator localC
      (LocalTrace.fieldStrengthSquarePolynomial readout))
  ≡ HaarLimit.physicalHaarExpectation physicalHaar
localCF2EqualsPhysicalHaarFromAsymptoticBridge
    {localTransport = localTransport}
    vanishing common =
  trans
    (sym (LocalLimit.finiteF2LimitIsPinnedLocalCF2 localTransport))
    (localFiniteF2LimitIsPhysicalHaar vanishing common)

------------------------------------------------------------------------
-- Backward compatibility: the old pointwise-common Q3 is the zero-error case.
------------------------------------------------------------------------

pointwiseCommonFiniteF2ToAsymptotic :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian localC embedding convention
      sequenceLimit readout localTransport physicalHaar}
    (vanishing : Vanishing.RealVanishingFiniteAlgebra sequenceLimit) →
    (∀ cutoff →
      HaarLimit.finiteCMP119Expectation physicalHaar cutoff
      ≡ LocalLimit.finiteF2Numerator localTransport cutoff) →
    AsymptoticCommonFiniteF2
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
      {readout = readout}
      localTransport physicalHaar
pointwiseCommonFiniteF2ToAsymptotic
    {localTransport = localTransport}
    {physicalHaar = physicalHaar}
    vanishing same =
  let
    zeroBound :
      ∀ cutoff →
      absℝ
        (HaarLimit.finiteCMP119Expectation physicalHaar cutoff
          -ℝ LocalLimit.finiteF2Numerator localTransport cutoff)
      ≤ℝ 0ℝ
    zeroBound cutoff
      rewrite same cutoff
            | subSelf (LocalLimit.finiteF2Numerator localTransport cutoff)
            | absZero =
      ≤ℝ-refl
  in record
    { AsymptoticCommonFiniteF2.bridgeError = λ _ → 0ℝ
    ; AsymptoticCommonFiniteF2.finiteF2BridgeBound = zeroBound
    ; AsymptoticCommonFiniteF2.bridgeErrorVanishes =
        Vanishing.vanishesZero vanishing
    }

------------------------------------------------------------------------
-- Frontier accounting.
------------------------------------------------------------------------

termwiseFiniteF2EqualityRequired : Bool
termwiseFiniteF2EqualityRequired = false

vanishingFiniteF2BridgeSufficesForCommonLimit : Bool
vanishingFiniteF2BridgeSufficesForCommonLimit = true

oldPointwiseQ3IsZeroErrorSpecialCase : Bool
oldPointwiseQ3IsZeroErrorSpecialCase = true

q3ReducedToAsymptoticFiniteF2Bridge : Bool
q3ReducedToAsymptoticFiniteF2Bridge = true

exactFiniteContinuumF2EqualityRequired : Bool
exactFiniteContinuumF2EqualityRequired = false
