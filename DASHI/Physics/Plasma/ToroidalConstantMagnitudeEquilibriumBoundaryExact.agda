module DASHI.Physics.Plasma.ToroidalConstantMagnitudeEquilibriumBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ToroidalConstantMagnitudeZeroBounceSeedExact as Seed
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- EQUILIBRIUM BOUNDARY FOR THE CONSTANT-|B| TOROIDAL SEED
--
-- The seed simultaneously pays constant |B| and div B = 0 on a circular
-- toroidal surface.  Ampere's law for the same field generally produces J_r
-- != 0, hence tangential components of J x B.  A static isotropic pressure
-- p=p(psi) cannot be silently used to absorb those tangential forces.
--
-- This boundary keeps three physically distinct continuation routes open:
--   (1) dynamic / Alfvenic flow balance,
--   (2) pressure-anisotropic equilibrium,
--   (3) more general 3-D field geometry whose current removes the tangential
--       Lorentz residual while preserving the zero-bounce invariant.
------------------------------------------------------------------------

record TangentialLorentzResidualReceipt : Set₁ where
  constructor tangential-lorentz-residual-receipt
  field
    radialCurrentReceipt : Set
    poloidalLorentzResidualReceipt : Set
    toroidalLorentzResidualReceipt : Set
    sameFieldAsConstantMagnitudeSeedReceipt : Set
    residualReference : String

open TangentialLorentzResidualReceipt public

record ConstantMagnitudeEquilibriumContinuation
    (population : ZeroBounce.DeclaredParticlePopulation)
    (seed : Seed.ToroidalConstantMagnitudeSeed population) : Set₁ where
  constructor constant-magnitude-equilibrium-continuation
  field
    tangentialResidual : TangentialLorentzResidualReceipt
    dynamicFlowBalanceRouteReceipt : Set
    anisotropicPressureRouteReceipt : Set
    threeDimensionalEquilibriumRouteReceipt : Set
    zeroBounceMustBePreservedReceipt : Set
    divergenceFreeMustBePreservedReceipt : Set
    continuationReference : String

open ConstantMagnitudeEquilibriumContinuation public

record ConstantMagnitudeEquilibriumBoundary : Set where
  constructor constant-magnitude-equilibrium-boundary
  field
    scalarPressureFluxFunctionAutomaticallyBalancesSeed : Bool
    scalarPressureFluxFunctionAutomaticallyBalancesSeedIsFalse :
      scalarPressureFluxFunctionAutomaticallyBalancesSeed ≡ false

    tangentialLorentzResidualMayBeIgnored : Bool
    tangentialLorentzResidualMayBeIgnoredIsFalse :
      tangentialLorentzResidualMayBeIgnored ≡ false

    dynamicFlowAnisotropyOr3DGeometryMayRemainSearchRoutes : Bool
    dynamicFlowAnisotropyOr3DGeometryMayRemainSearchRoutesIsTrue :
      dynamicFlowAnisotropyOr3DGeometryMayRemainSearchRoutes ≡ true

canonicalConstantMagnitudeEquilibriumBoundary : ConstantMagnitudeEquilibriumBoundary
canonicalConstantMagnitudeEquilibriumBoundary =
  constant-magnitude-equilibrium-boundary
    false refl
    false refl
    true refl

ampereReplayReference : String
ampereReplayReference =
  "scripts/toroidal_constantB_clebsch_probe.py::curl_components / lorentz_components"
