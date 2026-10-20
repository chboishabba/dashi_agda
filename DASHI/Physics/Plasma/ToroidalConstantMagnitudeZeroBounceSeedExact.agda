module DASHI.Physics.Plasma.ToroidalConstantMagnitudeZeroBounceSeedExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- CONSTANT-|B| TOROIDAL ZERO-BOUNCE SEED
--
-- Circular-torus coordinates with h_zeta = R0 + r cos(theta):
--
--   B_r     = 0
--   B_theta = C / h_zeta
--   B_zeta  = sqrt(B0^2 - C^2 / h_zeta^2)
--
-- on a surface where |C| < |B0| (R0-r).
--
-- Then h_zeta B_theta = C, so the axisymmetric divergence expression closes,
-- while B_theta^2 + B_zeta^2 = B0^2 pointwise.  Hence the adiabatic mirror
-- term vanishes on the declared surface.  Static scalar-pressure equilibrium
-- is deliberately NOT promoted here: curl(B) generally has a radial component
-- and J x B therefore has tangential components.
------------------------------------------------------------------------

record ToroidalConstantMagnitudeSeed
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor toroidal-constant-magnitude-seed
  field
    circularToroidalSurfaceReceipt : Set
    toroidalMetricFactorReceipt : Set
    radialFieldZeroReceipt : Set
    poloidalFieldFormulaReceipt : Set
    toroidalFieldFormulaReceipt : Set
    wholeSurfaceRealityConditionReceipt : Set

    constantMagneticMagnitudeReceipt : Set
    divergenceFreeFieldReceipt : Set
    zeroParallelMagnitudeGradientReceipt : Set
    zeroMagneticMirrorForceReceipt : Set
    zeroBounce : ZeroBounce.ZeroBounceReceipt population

    fieldLineTransformReceipt : Set
    guidingCentreCurvatureObservableReceipt : Set
    onePoloidalTurnRadialCurvatureClosureReceipt : Set
    seedReference : String

open ToroidalConstantMagnitudeSeed public

record ToroidalConstantMagnitudeBoundary : Set where
  constructor toroidal-constant-magnitude-boundary
  field
    constantMagnitudeAndDivergenceFreeCompatibleOnToroidalSurface : Bool
    constantMagnitudeAndDivergenceFreeCompatibleOnToroidalSurfaceIsTrue :
      constantMagnitudeAndDivergenceFreeCompatibleOnToroidalSurface ≡ true

    constantMagnitudeImpliesPointwiseZeroCurvatureDrift : Bool
    constantMagnitudeImpliesPointwiseZeroCurvatureDriftIsFalse :
      constantMagnitudeImpliesPointwiseZeroCurvatureDrift ≡ false

    thisSeedAlreadyProvesStaticScalarPressureEquilibrium : Bool
    thisSeedAlreadyProvesStaticScalarPressureEquilibriumIsFalse :
      thisSeedAlreadyProvesStaticScalarPressureEquilibrium ≡ false

    orbitalCurvatureClosureReplacesFiniteOrbitWidthAnalysis : Bool
    orbitalCurvatureClosureReplacesFiniteOrbitWidthAnalysisIsFalse :
      orbitalCurvatureClosureReplacesFiniteOrbitWidthAnalysis ≡ false

canonicalToroidalConstantMagnitudeBoundary : ToroidalConstantMagnitudeBoundary
canonicalToroidalConstantMagnitudeBoundary =
  toroidal-constant-magnitude-boundary
    true refl
    false refl
    false refl
    false refl

fieldFormulaReference : String
fieldFormulaReference =
  "B_r=0; B_theta=C/(R0+r cos theta); B_zeta=sqrt(B0^2-B_theta^2).  Executable arithmetic/orbit replay: scripts/toroidal_constantB_clebsch_probe.py"
