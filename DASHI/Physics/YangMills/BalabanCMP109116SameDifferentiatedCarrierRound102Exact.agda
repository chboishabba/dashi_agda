{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109116SameDifferentiatedCarrierRound102Exact where

------------------------------------------------------------------------
-- ROUND102 B->C SAME-OBJECT WELD
--
-- The source chain should not carry three independently supplied Hessians and
-- then ask for equalities between them.  CMP109 first constructs the effective
-- action and its E^(2)/Pi response; CMP116 localizes/differentiates that same
-- effective action on its analytic source coordinates; the Heat/Doob initial
-- potential is the negative log density generated from that same finite-cutoff
-- action.
--
-- This record therefore stores ONE effective potential and ONE declared second
-- variation coordinate.  The names consumed by CMP109, CMP116 and the static
-- term of the Heat/Doob log-Hessian are aliases.  Their same-object identities
-- are reflexive.  The physical source task is only to instantiate this carrier
-- with the actual finite-cutoff Bałaban density/coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record SameDifferentiatedEffectiveDensityCarrier : Set₁ where
  field
    Configuration Tangent Scalar : Set

    effectivePotential : Configuration → Scalar
    secondVariation : Configuration → Tangent → Tangent → Scalar

    -- Source declarations, deliberately propositions rather than duplicate data.
    cmp109EffectiveActionIsThisPotential : Set
    cmp109E2PiIsThisSecondVariation : Set
    cmp116LocalizedActivityIsThisPotential : Set
    cmp116HessianMarkIsThisSecondVariation : Set
    heatDoobInitialDensityIsExpMinusThisPotential : Set

open SameDifferentiatedEffectiveDensityCarrier public

cmp109SecondVariation :
  SameDifferentiatedEffectiveDensityCarrier →
  Configuration _ → Tangent _ → Tangent _ → Scalar _
cmp109SecondVariation dataSet = secondVariation dataSet

cmp116StaticHessian :
  SameDifferentiatedEffectiveDensityCarrier →
  Configuration _ → Tangent _ → Tangent _ → Scalar _
cmp116StaticHessian dataSet = secondVariation dataSet

heatDoobInitialStaticHessian :
  SameDifferentiatedEffectiveDensityCarrier →
  Configuration _ → Tangent _ → Tangent _ → Scalar _
heatDoobInitialStaticHessian dataSet = secondVariation dataSet

cmp109IsCMP116StaticHessian :
  (dataSet : SameDifferentiatedEffectiveDensityCarrier) →
  cmp109SecondVariation dataSet ≡ cmp116StaticHessian dataSet
cmp109IsCMP116StaticHessian dataSet = refl

cmp116IsHeatDoobInitialStaticHessian :
  (dataSet : SameDifferentiatedEffectiveDensityCarrier) →
  cmp116StaticHessian dataSet ≡ heatDoobInitialStaticHessian dataSet
cmp116IsHeatDoobInitialStaticHessian dataSet = refl

cmp109IsHeatDoobInitialStaticHessian :
  (dataSet : SameDifferentiatedEffectiveDensityCarrier) →
  cmp109SecondVariation dataSet ≡ heatDoobInitialStaticHessian dataSet
cmp109IsHeatDoobInitialStaticHessian dataSet = refl

sameDifferentiatedCarrierIdentityLevel : ProofLevel
sameDifferentiatedCarrierIdentityLevel = machineChecked

-- Physical seam: instantiate ONE carrier from the literal CMP109 finite-cutoff
-- effective density and CMP116 source coordinate.  CMP109 Sect.4/5 and CMP116
-- Sect.1 source the differentiated/localized construction, but this file does
-- not turn source prose into the missing same-density witness automatically.
literalCMP109116SameDifferentiatedCarrierInstantiationLevel : ProofLevel
literalCMP109116SameDifferentiatedCarrierInstantiationLevel = conditional
