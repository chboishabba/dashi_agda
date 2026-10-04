{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR136TraceAnomalyWeldExact where

------------------------------------------------------------------------
-- ALTERNATE SIGN ROUTE: R136 -> REAL TRACE ANOMALY.
--
-- The physical trace-anomaly capstone already proves the selected renormalized
-- CMP119 quantum trace is strictly negative in the ordered real carrier.  The
-- only new seam here is same-object identification of the embedded rational
-- R136 continuum response with that exact selected trace numerator.
--
-- This route deliberately concludes negativity of `embed Q_R136`.  The current
-- OrderedRationalRealEmbedding is strict-order preserving but does not expose
-- order reflection, so rational negativity is NOT inferred for free.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _<ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityRealPhysicalTraceAnomalyCapstoneExact as Capstone
import DASHI.Physics.Foundations.CMP119AntigravityRealTraceAnomalySameObjectExact as Anomaly
import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as GibbsPositive
import DASHI.Physics.Foundations.CMP119AntigravityRealFullSupportHaarExact as FullSupport
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as Gibbs
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder

record R136ToRealTraceAnomalyWeld
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
    embeddedR136IsSelectedQuantumTrace :
      Embed.embed embedding r136Response
      ≡
      Anomaly.selectedCMP119QuantumTraceNumerator
        (Capstone.anomalyWeld input)

open R136ToRealTraceAnomalyWeld public

embeddedR136ResponseNegative :
  ∀ {Configuration Action algebra quotientAuthority measure}
    (division : Division.RealDivisionAlgebra algebra quotientAuthority)
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
    (weld :
      R136ToRealTraceAnomalyWeld
        division laws strict embedding convention gibbs exponential fullSupport
        input r136Response) →
  Embed.embed embedding r136Response <ℝ 0ℝ
embeddedR136ResponseNegative
    division laws strict embedding convention gibbs exponential fullSupport
    input r136Response weld =
  subst
    (λ value → value <ℝ 0ℝ)
    (sym (embeddedR136IsSelectedQuantumTrace weld))
    (Capstone.selectedQuantumTraceNegative
      division laws strict embedding convention gibbs exponential fullSupport input)

alternateAnomalyRouteNeedsNoEq223SectorSignDecomposition : Bool
alternateAnomalyRouteNeedsNoEq223SectorSignDecomposition = true

alternateAnomalyRouteStillNeedsSameObjectR136TraceWeld : Bool
alternateAnomalyRouteStillNeedsSameObjectR136TraceWeld = true

rationalNegativityNotInferredWithoutOrderReflection : Bool
rationalNegativityNotInferredWithoutOrderReflection = true
