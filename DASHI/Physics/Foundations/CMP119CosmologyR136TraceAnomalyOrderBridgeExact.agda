{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR136TraceAnomalyOrderBridgeExact where

------------------------------------------------------------------------
-- EMBEDDED R136 ANOMALY SIGN -> RATIONAL R136 SIGN.
--
-- The concurrent anomaly weld proves
--
--   embed(Q_R136) < 0_R.
--
-- The ordered embedding currently exposes strict-order preservation but not
-- reflection.  Reuse the explicit zero-order-reflection authority rather than
-- silently treating rational and real order as definitionally identical.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _<ℝ_)

import DASHI.Physics.Foundations.CMP119CosmologyR136TraceAnomalyWeldExact as Anomaly
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as Order
import DASHI.Physics.Foundations.CMP119AntigravityRealPhysicalTraceAnomalyCapstoneExact as Capstone
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

rationalR136NegativeFromTraceAnomaly :
  ∀ {Configuration Action}
    {algebra : Cylinder.ScalarCylinderLimitAlgebra ℝ}
    {quotientAuthority :
      Quotient.RealQuotientConvergenceAuthority
        (Cylinder.Converges algebra)}
    (division : Division.RealDivisionAlgebra algebra quotientAuthority)
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure)
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
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
      Anomaly.R136ToRealTraceAnomalyWeld
        division laws strict embedding convention gibbs exponential fullSupport
        input r136Response) →
  r136Response < 0ℚ
rationalR136NegativeFromTraceAnomaly
    division laws strict embedding reflection convention gibbs exponential
    fullSupport input r136Response weld =
  Order.reflectNegative reflection r136Response
    (Anomaly.embeddedR136ResponseNegative
      division laws strict embedding convention gibbs exponential fullSupport
      input r136Response weld)

anomalyRouteRationalSignNeedsOnlyExplicitOrderReflection : Bool
anomalyRouteRationalSignNeedsOnlyExplicitOrderReflection = true
