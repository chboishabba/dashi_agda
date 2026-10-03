{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR136TraceAnomalyOrderDominanceExact where

------------------------------------------------------------------------
-- ALTERNATE SIGN ROUTE: ORDER DOMINANCE IS ENOUGH.
--
-- The previous fallback required exact same-object equality
--
--   embed Q_R136 = Q_anomaly.
--
-- Downstream uses only strict negativity.  Since the selected anomaly trace is
-- already strictly negative, the strictly weaker comparison
--
--   embed Q_R136 <= Q_anomaly
--
-- is sufficient.  Mixed weak/strict transitivity gives embed Q_R136 < 0, and
-- the already-owned negative-order reflection gives Q_R136 < 0.
--
-- Equality remains a sufficient producer of this comparison, but is no longer
-- the Pareto-minimal fallback obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_; _<ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119AntigravityRealPhysicalTraceAnomalyCapstoneExact as Capstone
import DASHI.Physics.Foundations.CMP119AntigravityRealTraceAnomalySameObjectExact as Anomaly
import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as GibbsPositive
import DASHI.Physics.Foundations.CMP119AntigravityRealFullSupportHaarExact as FullSupport
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as Order
import DASHI.Physics.Foundations.CMP119CosmologySelectedR109RealTailSignCompilerExact as RealOrder
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as Gibbs
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder

record R136ToRealTraceAnomalyUpperWeld
    {Configuration Action : Set}
    {algebra : Cylinder.ScalarCylinderLimitAlgebra ℝ}
    {quotientAuthority :
      Quotient.RealQuotientConvergenceAuthority
        (Cylinder.Converges algebra)}
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
    (fullSupport : FullSupport.FullSupportRealHaarAuthority measure)
    (input :
      Capstone.RealPhysicalTraceAnomalyInput
        algebra quotientAuthority division laws strict embedding convention
        gibbs exponential fullSupport)
    (r136Response : ℚ)
    : Set₁ where
  field
    embeddedR136BelowSelectedQuantumTrace :
      Embed.embed embedding r136Response
      ≤ℝ
      Anomaly.selectedCMP119QuantumTraceNumerator
        (Capstone.anomalyWeld input)

open R136ToRealTraceAnomalyUpperWeld public

embeddedR136ResponseNegativeFromUpperWeld :
  ∀ {Configuration Action algebra quotientAuthority measure}
    (division : Division.RealDivisionAlgebra algebra quotientAuthority)
    (laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure)
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (realOrder : RealOrder.RealWeakStrictTransitivity)
    (convention : Trace.RealSU2TraceConvention embedding)
    (gibbs :
      Gibbs.WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws)
    (exponential : GibbsPositive.StrictPositiveRealExponential)
    (fullSupport : FullSupport.FullSupportRealHaarAuthority measure)
    (input :
      Capstone.RealPhysicalTraceAnomalyInput
        algebra quotientAuthority division laws strict embedding convention
        gibbs exponential fullSupport)
    (r136Response : ℚ)
    (weld :
      R136ToRealTraceAnomalyUpperWeld
        division laws strict embedding convention gibbs exponential fullSupport
        input r136Response) →
  Embed.embed embedding r136Response <ℝ
    DASHI.Foundations.RealAnalysisAxioms.0ℝ
embeddedR136ResponseNegativeFromUpperWeld
    division laws strict embedding realOrder convention gibbs exponential
    fullSupport input r136Response weld =
  RealOrder.weakThenStrict realOrder
    (embeddedR136BelowSelectedQuantumTrace weld)
    (Capstone.selectedQuantumTraceNegative
      division laws strict embedding convention gibbs exponential fullSupport input)

rationalR136NegativeFromUpperWeld :
  ∀ {Configuration Action algebra quotientAuthority measure}
    (division : Division.RealDivisionAlgebra algebra quotientAuthority)
    (laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure)
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (realOrder : RealOrder.RealWeakStrictTransitivity)
    (reflection : Order.NegativeOrderReflectionAtZero embedding)
    (convention : Trace.RealSU2TraceConvention embedding)
    (gibbs :
      Gibbs.WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws)
    (exponential : GibbsPositive.StrictPositiveRealExponential)
    (fullSupport : FullSupport.FullSupportRealHaarAuthority measure)
    (input :
      Capstone.RealPhysicalTraceAnomalyInput
        algebra quotientAuthority division laws strict embedding convention
        gibbs exponential fullSupport)
    (r136Response : ℚ)
    (weld :
      R136ToRealTraceAnomalyUpperWeld
        division laws strict embedding convention gibbs exponential fullSupport
        input r136Response) →
  r136Response < 0ℚ
rationalR136NegativeFromUpperWeld
    division laws strict embedding realOrder reflection convention gibbs exponential
    fullSupport input r136Response weld =
  Order.reflectNegative reflection r136Response
    (embeddedR136ResponseNegativeFromUpperWeld
      division laws strict embedding realOrder convention gibbs exponential
      fullSupport input r136Response weld)

anomalyFallbackExactEqualityIsParetoOverstrong : Bool
anomalyFallbackExactEqualityIsParetoOverstrong = true

anomalyFallbackOneSidedUpperComparisonSuffices : Bool
anomalyFallbackOneSidedUpperComparisonSuffices = true

remainingFallbackPhysicalLeafIsR136BelowSelectedAnomalyTrace : Bool
remainingFallbackPhysicalLeafIsR136BelowSelectedAnomalyTrace = true

anomalyOrderDominanceCompilerLevel : ProofLevel
anomalyOrderDominanceCompilerLevel = machineChecked
