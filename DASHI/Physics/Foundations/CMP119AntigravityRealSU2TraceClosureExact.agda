{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _<ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.Foundations.CMP119AntigravityRealHaarStrictPositivityExact as Haar
import DASHI.Physics.Foundations.CMP119AntigravitySU2TraceConventionExact as SU2
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- REAL SU(2) RENORMALIZED TRACE SIGN ON THE LITERAL CMP119 HAAR MEASURE
--
-- Physical convention:
--
--   b_trace = embed(-11/48) * (1/pi^2)
--   Q_trace = b_trace * N(F^2)
--
-- with all factors living in the same real scalar carrier as the literal
-- CMP119 finite measure.
------------------------------------------------------------------------

record RealSU2TraceConvention
    (embedding : Embed.OrderedRationalRealEmbedding) : Set₁ where
  field
    inversePiSquared : ℝ
    inversePiSquaredPositive :
      0ℝ <ℝ inversePiSquared

open RealSU2TraceConvention public

realSU2TraceCoefficient :
  Embed.OrderedRationalRealEmbedding →
  RealSU2TraceConvention _ →
  ℝ
realSU2TraceCoefficient embedding convention =
  Embed.embed embedding SU2.su2TraceRationalCoefficient
    *ℝ inversePiSquared convention

embeddedSU2RationalTraceCoefficientNegative :
  (embedding : Embed.OrderedRationalRealEmbedding) →
  Embed.embed embedding SU2.su2TraceRationalCoefficient <ℝ 0ℝ
embeddedSU2RationalTraceCoefficientNegative embedding =
  subst
    (λ right →
      Embed.embed embedding SU2.su2TraceRationalCoefficient <ℝ right)
    (Embed.zeroExact embedding)
    (Embed.strictOrderPreserving embedding
      SU2.su2TraceCoefficientNegative)

realSU2TraceCoefficientNegative :
  (strict : Strict.RealStrictSignLaws)
  (embedding : Embed.OrderedRationalRealEmbedding)
  (convention : RealSU2TraceConvention embedding) →
  realSU2TraceCoefficient embedding convention <ℝ 0ℝ
realSU2TraceCoefficientNegative strict embedding convention =
  Strict.negativeTimesPositive strict
    (embeddedSU2RationalTraceCoefficientNegative embedding)
    (inversePiSquaredPositive convention)

record RealSU2TraceAttachment
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : RealSU2TraceConvention embedding)
    (ordered : Haar.OrderedRealHaarIntegrationLaws measure) : Set₁ where
  field
    fieldStrengthSquare : Configuration → ℝ

    positiveWeightedF2 :
      Haar.PositiveWeightedRealHaarWitness
        ordered fieldStrengthSquare

    selectedQuantumTraceNumerator : ℝ

    selectedTraceUsesPhysicalSU2Convention :
      selectedQuantumTraceNumerator
      ≡
      realSU2TraceCoefficient embedding convention
      *ℝ
      Haar.weightedNumerator
        {measure = measure}
        fieldStrengthSquare

open RealSU2TraceAttachment public

realFieldStrengthSquareNumeratorPositive :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : RealSU2TraceConvention embedding)
    (ordered : Haar.OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure)
    (attachment :
      RealSU2TraceAttachment
        strict embedding convention ordered) →
  0ℝ <ℝ
    Haar.weightedNumerator
      {measure = measure}
      (fieldStrengthSquare attachment)
realFieldStrengthSquareNumeratorPositive
    strict embedding convention ordered attachment =
  Haar.weightedNumeratorPositive
    strict ordered
    (fieldStrengthSquare attachment)
    (positiveWeightedF2 attachment)

realSelectedQuantumTraceNegative :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : RealSU2TraceConvention embedding)
    (ordered : Haar.OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure)
    (attachment :
      RealSU2TraceAttachment
        strict embedding convention ordered) →
  selectedQuantumTraceNumerator attachment <ℝ 0ℝ
realSelectedQuantumTraceNegative
    strict embedding convention ordered attachment =
  subst
    (λ value → value <ℝ 0ℝ)
    (sym (selectedTraceUsesPhysicalSU2Convention attachment))
    (Strict.negativeTimesPositive strict
      (realSU2TraceCoefficientNegative strict embedding convention)
      (realFieldStrengthSquareNumeratorPositive
        strict embedding convention ordered attachment))

record RealSelectedActiveConnectedTraceWeld
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : RealSU2TraceConvention embedding)
    (ordered : Haar.OrderedRealHaarIntegrationLaws measure)
    (traceAttachment :
      RealSU2TraceAttachment
        strict embedding convention ordered) : Set₁ where
  field
    selectedActiveConnectedNumerator : ℝ

    selectedActiveIsPartitionTimesQuantumTrace :
      selectedActiveConnectedNumerator
      ≡
      Physical.partitionFunction measure
      *ℝ
      selectedQuantumTraceNumerator traceAttachment

open RealSelectedActiveConnectedTraceWeld public

selectedRealActiveConnectedNumeratorNegative :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : RealSU2TraceConvention embedding)
    (ordered : Haar.OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure)
    (partitionWitness : Haar.PositiveRealPartitionWitness ordered)
    (traceAttachment :
      RealSU2TraceAttachment
        strict embedding convention ordered)
    (activeWeld :
      RealSelectedActiveConnectedTraceWeld
        strict embedding convention ordered traceAttachment) →
  selectedActiveConnectedNumerator activeWeld <ℝ 0ℝ
selectedRealActiveConnectedNumeratorNegative
    {measure = measure}
    strict embedding convention ordered partitionWitness
    traceAttachment activeWeld =
  subst
    (λ value → value <ℝ 0ℝ)
    (sym (selectedActiveIsPartitionTimesQuantumTrace activeWeld))
    (Strict.positiveTimesNegative strict
      (Haar.partitionFunctionPositive
        strict ordered partitionWitness)
      (realSelectedQuantumTraceNegative
        strict embedding convention ordered traceAttachment))
