module DASHI.Physics.Plasma.ToroidalConstantMagnitudeGeodesic3DEquilibriumExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ToroidalConstantMagnitudeZeroBounceSeedExact as Seed
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- ROUTE C: STATIC SCALAR-PRESSURE 3-D GEOMETRY
--
-- With |B| constant and div B = 0,
--
--   J x B = (B . grad) B / mu0 = (B^2/mu0) kappa.
--
-- If p = p(psi), grad p is normal to each flux surface.  Therefore the
-- tangential component of kappa must vanish.  Geometrically, each magnetic
-- field line must be a geodesic of its flux surface; the normal curvature then
-- supplies the scalar-pressure force balance.
--
-- This owner promotes only that exact necessary/sufficient geometric shape.
-- The current circular-torus seed does not automatically inhabit it.
------------------------------------------------------------------------

record GeodesicFluxSurfaceBalanceReceipt
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor geodesic-flux-surface-balance-receipt
  field
    nestedFluxSurfaceReceipt : Set
    constantMagnitudeFieldReceipt : Set
    divergenceFreeFieldReceipt : Set
    fieldTangentToFluxSurfaceReceipt : Set
    tangentialCurvatureZeroReceipt : Set
    fieldLinesGeodesicOnSurfaceReceipt : Set
    normalCurvatureMatchesPressureGradientReceipt : Set
    scalarPressureFluxFunctionReceipt : Set
    zeroBouncePreservedReceipt : Set
    finiteOrbitWidthReceipt : Set
    threeDimensionalEmbeddingReceipt : Set
    receiptReference : String

open GeodesicFluxSurfaceBalanceReceipt public

record Geodesic3DBoundary : Set where
  constructor geodesic-3d-boundary
  field
    forceFreeConstantMagnitudeCurvedToroidalShortcutAvailable : Bool
    forceFreeConstantMagnitudeCurvedToroidalShortcutAvailableIsFalse :
      forceFreeConstantMagnitudeCurvedToroidalShortcutAvailable ≡ false

    scalarPressureRequiresTangentialCurvatureZero : Bool
    scalarPressureRequiresTangentialCurvatureZeroIsTrue :
      scalarPressureRequiresTangentialCurvatureZero ≡ true

    tangentialCurvatureZeroIsGeodesicCondition : Bool
    tangentialCurvatureZeroIsGeodesicConditionIsTrue :
      tangentialCurvatureZeroIsGeodesicCondition ≡ true

    circularToroidalSeedAlreadyProvesGeodesicCondition : Bool
    circularToroidalSeedAlreadyProvesGeodesicConditionIsFalse :
      circularToroidalSeedAlreadyProvesGeodesicCondition ≡ false

canonicalGeodesic3DBoundary : Geodesic3DBoundary
canonicalGeodesic3DBoundary =
  geodesic-3d-boundary
    false refl
    true refl
    true refl
    false refl

geodesicBalanceReference : String
geodesicBalanceReference =
  "For constant |B|: JxB=(B^2/mu0)kappa. If p=p(psi), tangential kappa must vanish; magnetic field lines are geodesics of the flux surface and normal curvature carries grad p."
