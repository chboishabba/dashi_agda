{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealPhysicalTraceSourceExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _<ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.Foundations.CMP119AntigravityRealPartitionStrictPositivityExact as Partition
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealF2StrictPositivityFromFullSupportExact as F2Positive
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as GibbsPositive
import DASHI.Physics.Foundations.CMP119AntigravityRealFullSupportHaarExact as FullSupport
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as Gibbs
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient

------------------------------------------------------------------------
-- PREFERRED REAL PHYSICAL TRACE SOURCE
--
-- Inputs now separate cleanly into:
--
-- STANDARD / ALGEBRA:
--   * ordered-real strict sign laws;
--   * rational -> real ordered embedding;
--   * positive inverse-pi-square convention;
--   * full-support compact-Haar strict integration;
--   * semantic meaning of the finite-family Nonzero token.
--
-- SAME-OBJECT PHYSICS:
--   * real Wilson/Gibbs density = exp(-S);
--   * selected renormalized trace = b_trace * N(F^2);
--   * selected active connected numerator = Z * Q_trace.
--
-- CONSTRUCTED CONSEQUENCES:
--   Z > 0, N(F^2) > 0, b_trace < 0, Q_trace < 0, C_active < 0.
------------------------------------------------------------------------

record RealPhysicalTraceSourceInput
    {Configuration Action : Set}
    {Converges}
    (authority : Quotient.RealQuotientConvergenceAuthority Converges)
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure)
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : Trace.RealSU2TraceConvention embedding)
    (gibbs :
      Gibbs.WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws)
    (exponential : GibbsPositive.StrictPositiveRealExponential)
    (fullSupport : FullSupport.FullSupportRealHaarAuthority measure) : Set₁ where
  field
    quotientNonzeroSemantics :
      Partition.QuotientNonzeroSemantics authority

    partitionNonzero :
      Quotient.Nonzero authority
        (Physical.partitionFunction measure)

    f2Positivity :
      F2Positive.RealPhysicalF2StrictPositivityInput
        strict embedding gibbs exponential fullSupport

    selectedQuantumTraceNumerator : ℝ

    selectedTraceUsesPhysicalSU2Convention :
      selectedQuantumTraceNumerator
      ≡
      Trace.realSU2TraceCoefficient embedding convention
      *ℝ
      F2Positive.weightedF2Numerator
        {measure = measure}
        (F2Positive.F2.realFieldStrengthSquare
          (F2Positive.curvature f2Positivity))

    selectedActiveConnectedNumerator : ℝ

    selectedActiveIsPartitionTimesQuantumTrace :
      selectedActiveConnectedNumerator
      ≡
      Physical.partitionFunction measure
      *ℝ selectedQuantumTraceNumerator

open RealPhysicalTraceSourceInput public

physicalPartitionStrictlyPositive :
  ∀ {Configuration Action Converges authority measure}
    (laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure)
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : Trace.RealSU2TraceConvention embedding)
    (gibbs :
      Gibbs.WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws)
    (exponential : GibbsPositive.StrictPositiveRealExponential)
    (fullSupport : FullSupport.FullSupportRealHaarAuthority measure)
    (input :
      RealPhysicalTraceSourceInput
        {Converges = Converges}
        authority laws strict embedding convention
        gibbs exponential fullSupport) →
  0ℝ <ℝ Physical.partitionFunction measure
physicalPartitionStrictlyPositive
    laws strict embedding convention gibbs exponential fullSupport input =
  Partition.partitionFunctionStrictlyPositive
    strict laws
    (quotientNonzeroSemantics input)
    (partitionNonzero input)

physicalF2NumeratorStrictlyPositive :
  ∀ {Configuration Action Converges authority measure}
    (laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure)
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : Trace.RealSU2TraceConvention embedding)
    (gibbs :
      Gibbs.WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws)
    (exponential : GibbsPositive.StrictPositiveRealExponential)
    (fullSupport : FullSupport.FullSupportRealHaarAuthority measure)
    (input :
      RealPhysicalTraceSourceInput
        {Converges = Converges}
        authority laws strict embedding convention
        gibbs exponential fullSupport) →
  0ℝ <ℝ
    F2Positive.weightedF2Numerator
      {measure = measure}
      (F2Positive.F2.realFieldStrengthSquare
        (F2Positive.curvature (f2Positivity input)))
physicalF2NumeratorStrictlyPositive
    laws strict embedding convention gibbs exponential fullSupport input =
  F2Positive.realPhysicalF2NumeratorStrictlyPositive
    strict embedding fullSupport
    (f2Positivity input)

physicalQuantumTraceStrictlyNegative :
  ∀ {Configuration Action Converges authority measure}
    (laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure)
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : Trace.RealSU2TraceConvention embedding)
    (gibbs :
      Gibbs.WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws)
    (exponential : GibbsPositive.StrictPositiveRealExponential)
    (fullSupport : FullSupport.FullSupportRealHaarAuthority measure)
    (input :
      RealPhysicalTraceSourceInput
        {Converges = Converges}
        authority laws strict embedding convention
        gibbs exponential fullSupport) →
  selectedQuantumTraceNumerator input <ℝ 0ℝ
physicalQuantumTraceStrictlyNegative
    laws strict embedding convention gibbs exponential fullSupport input =
  subst
    (λ value → value <ℝ 0ℝ)
    (sym (selectedTraceUsesPhysicalSU2Convention input))
    (Strict.negativeTimesPositive strict
      (Trace.realSU2TraceCoefficientNegative
        strict embedding convention)
      (physicalF2NumeratorStrictlyPositive
        laws strict embedding convention gibbs exponential fullSupport input))

physicalActiveConnectedNumeratorStrictlyNegative :
  ∀ {Configuration Action Converges authority measure}
    (laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure)
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : Trace.RealSU2TraceConvention embedding)
    (gibbs :
      Gibbs.WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws)
    (exponential : GibbsPositive.StrictPositiveRealExponential)
    (fullSupport : FullSupport.FullSupportRealHaarAuthority measure)
    (input :
      RealPhysicalTraceSourceInput
        {Converges = Converges}
        authority laws strict embedding convention
        gibbs exponential fullSupport) →
  selectedActiveConnectedNumerator input <ℝ 0ℝ
physicalActiveConnectedNumeratorStrictlyNegative
    laws strict embedding convention gibbs exponential fullSupport input =
  subst
    (λ value → value <ℝ 0ℝ)
    (sym (selectedActiveIsPartitionTimesQuantumTrace input))
    (Strict.positiveTimesNegative strict
      (physicalPartitionStrictlyPositive
        laws strict embedding convention gibbs exponential fullSupport input)
      (physicalQuantumTraceStrictlyNegative
        laws strict embedding convention gibbs exponential fullSupport input))
