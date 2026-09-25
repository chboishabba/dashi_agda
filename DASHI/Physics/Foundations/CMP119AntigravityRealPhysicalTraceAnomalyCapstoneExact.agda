{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealPhysicalTraceAnomalyCapstoneExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _<ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.Foundations.CMP119AntigravityRealPartitionStrictPositivityExact as Partition
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealF2StrictPositivityFromFullSupportExact as F2Positive
import DASHI.Physics.Foundations.CMP119AntigravityRealCurvatureF2PointBridgeExact as F2
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as GibbsPositive
import DASHI.Physics.Foundations.CMP119AntigravityRealFullSupportHaarExact as FullSupport
import DASHI.Physics.Foundations.CMP119AntigravityRealTraceAnomalySameObjectExact as Anomaly
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as Gibbs
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder

------------------------------------------------------------------------
-- PREFERRED REAL PHYSICAL TRACE-ANOMALY CAPSTONE
--
-- Unlike the earlier direct capstone, this record does NOT accept
--
--   selectedTrace = b_trace * selectedF2
--
-- as a free field.  It must be produced from:
--
--   (a) a sourced renormalized pure-YM trace-anomaly theorem;
--   (b) a CMP119 -> renormalized same-object weld for trace and F^2;
--   (c) equality of that selected F^2 numerator with the literal real
--       Wilson/Gibbs weighted F^2 numerator used by the positivity theorem.
------------------------------------------------------------------------

record RealPhysicalTraceAnomalyInput
    {Configuration Action : Set}
    (algebra : Cylinder.ScalarCylinderLimitAlgebra ℝ)
    (quotientAuthority :
      Quotient.RealQuotientConvergenceAuthority
        (Cylinder.Converges algebra))
    (division : Division.RealDivisionAlgebra algebra quotientAuthority)
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
    partitionNonzero :
      Quotient.Nonzero quotientAuthority
        (Physical.partitionFunction measure)

    f2Positivity :
      F2Positive.RealPhysicalF2StrictPositivityInput
        strict embedding gibbs exponential fullSupport

    anomalyAuthority :
      Anomaly.RenormalizedPureYMTraceAnomalyAuthority
        embedding convention

    anomalyWeld :
      Anomaly.CMP119ToRenormalizedTraceAnomalyWeld
        anomalyAuthority

    selectedAnomalyF2IsPhysicalWeightedF2 :
      Anomaly.selectedCMP119F2Numerator anomalyWeld
      ≡
      F2Positive.weightedF2Numerator
        {measure = measure}
        (F2.realFieldStrengthSquare
          (F2Positive.curvature f2Positivity))

    selectedActiveConnectedNumerator : ℝ

    selectedActiveIsPartitionTimesQuantumTrace :
      selectedActiveConnectedNumerator
      ≡
      Physical.partitionFunction measure
      *ℝ
      Anomaly.selectedCMP119QuantumTraceNumerator anomalyWeld

open RealPhysicalTraceAnomalyInput public

selectedCMP119TraceIdentity :
  ∀ {Configuration Action algebra quotientAuthority measure}
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
      RealPhysicalTraceAnomalyInput
        algebra quotientAuthority division laws strict embedding convention
        gibbs exponential fullSupport) →
  Anomaly.selectedCMP119QuantumTraceNumerator (anomalyWeld input)
  ≡
  Trace.realSU2TraceCoefficient embedding convention
  *ℝ
  F2Positive.weightedF2Numerator
    {measure = measure}
    (F2.realFieldStrengthSquare
      (F2Positive.curvature (f2Positivity input)))
selectedCMP119TraceIdentity
    laws strict embedding convention gibbs exponential fullSupport input =
  trans
    (Anomaly.selectedCMP119TraceIsPhysicalSU2BetaF2
      (anomalyWeld input))
    (cong
      (λ value →
        Trace.realSU2TraceCoefficient embedding convention
        *ℝ value)
      (selectedAnomalyF2IsPhysicalWeightedF2 input))

partitionPositive :
  ∀ {Configuration Action algebra quotientAuthority measure}
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
      RealPhysicalTraceAnomalyInput
        algebra quotientAuthority division laws strict embedding convention
        gibbs exponential fullSupport) →
  0ℝ <ℝ Physical.partitionFunction measure
partitionPositive
    laws strict embedding convention gibbs exponential fullSupport input =
  Partition.partitionFunctionStrictlyPositive
    strict laws
    (Partition.quotientNonzeroSemanticsFromDivision
      strict division)
    (partitionNonzero input)

f2NumeratorPositive :
  ∀ {Configuration Action algebra quotientAuthority measure}
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
      RealPhysicalTraceAnomalyInput
        algebra quotientAuthority division laws strict embedding convention
        gibbs exponential fullSupport) →
  0ℝ <ℝ
  F2Positive.weightedF2Numerator
    {measure = measure}
    (F2.realFieldStrengthSquare
      (F2Positive.curvature (f2Positivity input)))
f2NumeratorPositive
    laws strict embedding convention gibbs exponential fullSupport input =
  F2Positive.realPhysicalF2NumeratorStrictlyPositive
    strict embedding fullSupport
    (f2Positivity input)

selectedQuantumTraceNegative :
  ∀ {Configuration Action algebra quotientAuthority measure}
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
      RealPhysicalTraceAnomalyInput
        algebra quotientAuthority division laws strict embedding convention
        gibbs exponential fullSupport) →
  Anomaly.selectedCMP119QuantumTraceNumerator (anomalyWeld input) <ℝ 0ℝ
selectedQuantumTraceNegative
    laws strict embedding convention gibbs exponential fullSupport input =
  subst
    (λ value → value <ℝ 0ℝ)
    (sym
      (selectedCMP119TraceIdentity
        laws strict embedding convention gibbs exponential fullSupport input))
    (Strict.negativeTimesPositive strict
      (Trace.realSU2TraceCoefficientNegative
        strict embedding convention)
      (f2NumeratorPositive
        laws strict embedding convention gibbs exponential fullSupport input))

selectedActiveConnectedNumeratorNegative :
  ∀ {Configuration Action algebra quotientAuthority measure}
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
      RealPhysicalTraceAnomalyInput
        algebra quotientAuthority division laws strict embedding convention
        gibbs exponential fullSupport) →
  selectedActiveConnectedNumerator input <ℝ 0ℝ
selectedActiveConnectedNumeratorNegative
    laws strict embedding convention gibbs exponential fullSupport input =
  subst
    (λ value → value <ℝ 0ℝ)
    (sym (selectedActiveIsPartitionTimesQuantumTrace input))
    (Strict.positiveTimesNegative strict
      (partitionPositive
        laws strict embedding convention gibbs exponential fullSupport input)
      (selectedQuantumTraceNegative
        laws strict embedding convention gibbs exponential fullSupport input))
