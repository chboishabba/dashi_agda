{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanHeatDoobSameDensityLogHessianRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC2: SAME-DENSITY HEAT/DOOB FIRST/SECOND DERIVATIVE IDENTITY
--
-- For u_t = H_t(exp(-V)) and V_t = -log u_t, the tilted conditional density
-- proportional to the heat kernel times exp(-V) gives the standard identity
--
--   Hess V_t[u,v]
--     = E_t[ Hess V[u,v] ]
--       - Cov_t( dV[u], dV[v] ).
--
-- The identity is standard differentiation/probability.  The Yang--Mills content
-- is SAME-DENSITY identification: V is the literal finite-cutoff effective
-- potential carried by the Round103 CMP109/CMP116 carrier, and the first/second
-- variations are those of that exact potential.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source

record HeatDoobSameDensityCalculus
    (carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier) : Set₁ where
  field
    Time Scalar : Set

    subtract : Scalar → Scalar → Scalar

    -- The literal conditional/titled expectation induced from H_t exp(-V).
    conditionalExpectedHessian :
      Time → Source.Background (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier) → Scalar

    conditionalGradientCovariance :
      Time → Source.Background (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier) → Scalar

    heatDoobHessian :
      Time → Source.Background (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier) →
      Source.Tangent (Carrier.source carrier) → Scalar

    -- These are the literal density/derivative identifications.  They prevent a
    -- generic comparison Gibbs measure from being substituted silently.
    heatInitialPotentialIsCarrierPotential : Set
    conditionalDensityIsHeatTiltOfCarrierPotential : Set
    firstGradientIsCarrierFirstVariation : Set
    expectedStaticHessianIsCarrierSecondVariation : Set

    -- Standard log-heat differentiation theorem on that same density.
    logHeatHessianIdentity : ∀ time background u v →
      heatDoobHessian time background u v
      ≡ subtract
          (conditionalExpectedHessian time background u v)
          (conditionalGradientCovariance time background u v)

open HeatDoobSameDensityCalculus public

heatDoobHessianIsStaticMinusCovariance :
  ∀ {carrier}
    (dataSet : HeatDoobSameDensityCalculus carrier) →
  ∀ time background u v →
  heatDoobHessian dataSet time background u v
  ≡ subtract dataSet
      (conditionalExpectedHessian dataSet time background u v)
      (conditionalGradientCovariance dataSet time background u v)
heatDoobHessianIsStaticMinusCovariance dataSet =
  logHeatHessianIdentity dataSet

sameDensityHeatDoobIdentityWiringLevel : ProofLevel
sameDensityHeatDoobIdentityWiringLevel = machineChecked

heatDoobLogHessianConditionalCovarianceIdentityLevel : ProofLevel
heatDoobLogHessianConditionalCovarianceIdentityLevel = standardImported

-- Physical/source seam remaining after BC1: instantiate the heat semigroup and
-- tilted conditional density on the SAME finite-cutoff potential.  No new RG
-- localization theorem is part of this identity.
literalYMSameDensityHeatDoobIdentificationLevel : ProofLevel
literalYMSameDensityHeatDoobIdentificationLevel = conditional
