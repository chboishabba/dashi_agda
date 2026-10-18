{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealSU2RegionTraceCapstoneExact where

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _<ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.Foundations.CMP119AntigravityRealHaarStrictPositivityExact as Haar
import DASHI.Physics.Foundations.CMP119AntigravityRealHaarRegionSourceSignsExact as RegionSigns
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as Trace
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- REAL PHYSICAL SOURCE CAPSTONE
--
-- One positive-mass nonzero-curvature Haar region supplies Z>0 and N(F^2)>0.
-- The convention attachment supplies
--
--   Q_trace = [embed(-11/48) / pi^2] N(F^2).
--
-- The same-object active-source weld supplies
--
--   C_active = Z Q_trace.
--
-- Hence C_active < 0 on the literal real CMP119 finite measure.
------------------------------------------------------------------------

record RealSU2RegionTraceSourceInput
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : Trace.RealSU2TraceConvention embedding)
    (ordered : Haar.OrderedRealHaarIntegrationLaws measure) : Set₁ where
  field
    fieldStrengthSquare : Configuration → ℝ

    regionSigns :
      RegionSigns.RealHaarRegionSourceSignInput
        ordered fieldStrengthSquare

    selectedQuantumTraceNumerator : ℝ

    selectedTraceUsesPhysicalSU2Convention :
      selectedQuantumTraceNumerator
      ≡
      Trace.realSU2TraceCoefficient embedding convention
      *ℝ
      Haar.weightedNumerator
        {measure = measure}
        fieldStrengthSquare

open RealSU2RegionTraceSourceInput public

asTraceAttachment :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : Trace.RealSU2TraceConvention embedding)
    (ordered : Haar.OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure) →
  (input :
    RealSU2RegionTraceSourceInput
      strict embedding convention ordered) →
  Trace.RealSU2TraceAttachment
    strict embedding convention ordered
asTraceAttachment strict embedding convention ordered input = record
  { Trace.RealSU2TraceAttachment.fieldStrengthSquare =
      fieldStrengthSquare input
  ; Trace.RealSU2TraceAttachment.positiveWeightedF2 =
      RegionSigns.asWeightedF2Witness
        strict (regionSigns input)
  ; Trace.RealSU2TraceAttachment.selectedQuantumTraceNumerator =
      selectedQuantumTraceNumerator input
  ; Trace.RealSU2TraceAttachment.selectedTraceUsesPhysicalSU2Convention =
      selectedTraceUsesPhysicalSU2Convention input
  }

regionTracePartitionPositive :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : Trace.RealSU2TraceConvention embedding)
    (ordered : Haar.OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure)
    (input :
      RealSU2RegionTraceSourceInput
        strict embedding convention ordered) →
  0ℝ <ℝ Physical.partitionFunction measure
regionTracePartitionPositive strict embedding convention ordered input =
  RegionSigns.regionSourcePartitionPositive
    strict ordered
    (fieldStrengthSquare input)
    (regionSigns input)

regionTraceF2NumeratorPositive :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : Trace.RealSU2TraceConvention embedding)
    (ordered : Haar.OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure)
    (input :
      RealSU2RegionTraceSourceInput
        strict embedding convention ordered) →
  0ℝ <ℝ
    Haar.weightedNumerator
      {measure = measure}
      (fieldStrengthSquare input)
regionTraceF2NumeratorPositive strict embedding convention ordered input =
  RegionSigns.regionSourceF2NumeratorPositive
    strict ordered
    (fieldStrengthSquare input)
    (regionSigns input)

regionTraceQuantumTraceNegative :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : Trace.RealSU2TraceConvention embedding)
    (ordered : Haar.OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure)
    (input :
      RealSU2RegionTraceSourceInput
        strict embedding convention ordered) →
  selectedQuantumTraceNumerator input <ℝ 0ℝ
regionTraceQuantumTraceNegative
    strict embedding convention ordered input =
  Trace.realSelectedQuantumTraceNegative
    strict embedding convention ordered
    (asTraceAttachment strict embedding convention ordered input)

record RealSU2RegionActiveSourceWeld
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : Trace.RealSU2TraceConvention embedding)
    (ordered : Haar.OrderedRealHaarIntegrationLaws measure)
    (input :
      RealSU2RegionTraceSourceInput
        strict embedding convention ordered) : Set₁ where
  field
    selectedActiveConnectedNumerator : ℝ

    selectedActiveIsPartitionTimesQuantumTrace :
      selectedActiveConnectedNumerator
      ≡
      Physical.partitionFunction measure
      *ℝ
      selectedQuantumTraceNumerator input

open RealSU2RegionActiveSourceWeld public

realSU2RegionActiveSourceNegative :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : Trace.RealSU2TraceConvention embedding)
    (ordered : Haar.OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure)
    (input :
      RealSU2RegionTraceSourceInput
        strict embedding convention ordered)
    (active :
      RealSU2RegionActiveSourceWeld
        strict embedding convention ordered input) →
  selectedActiveConnectedNumerator active <ℝ 0ℝ
realSU2RegionActiveSourceNegative
    {measure = measure}
    strict embedding convention ordered input active =
  let
    traceAttachment =
      asTraceAttachment strict embedding convention ordered input

    traceActive :
      Trace.RealSelectedActiveConnectedTraceWeld
        strict embedding convention ordered traceAttachment
    traceActive = record
      { Trace.RealSelectedActiveConnectedTraceWeld.selectedActiveConnectedNumerator =
          selectedActiveConnectedNumerator active
      ; Trace.RealSelectedActiveConnectedTraceWeld.selectedActiveIsPartitionTimesQuantumTrace =
          selectedActiveIsPartitionTimesQuantumTrace active
      }
  in
  Trace.selectedRealActiveConnectedNumeratorNegative
    strict embedding convention ordered
    (RegionSigns.asPartitionWitness
      strict (regionSigns input))
    traceAttachment traceActive
