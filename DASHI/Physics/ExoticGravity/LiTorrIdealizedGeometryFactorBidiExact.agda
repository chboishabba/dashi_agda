module DASHI.Physics.ExoticGravity.LiTorrIdealizedGeometryFactorBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- IDEALIZED GEOMETRY FACTOR FOR LI/TORR MICROSCOPIC-TO-BULK SCALING
--
-- Purpose: separate the harmless arithmetic N * B_ion from the physical
-- geometry/orientation factor needed to turn microscopic source contributions
-- into one external gravitomagnetic field.  This is a structural owner; it
-- does not assert the historical apparatus had this idealized geometry.
------------------------------------------------------------------------

data IdealizedSourceShape : Set where
  thinRing : IdealizedSourceShape
  uniformCylinder : IdealizedSourceShape
  unresolvedHistoricalShape : IdealizedSourceShape

record IdealizedSource : Set where
  constructor idealized-source
  field
    shape : IdealizedSourceShape
    totalMass radius length angularVelocity : String
    totalAngularMomentum : String
    observationDistance : String

open IdealizedSource public

------------------------------------------------------------------------
-- Same-total-angular-momentum comparison.
--
-- In ordinary stationary weak-field GR, the external dipole-scale field of a
-- compact rotating source is controlled by total angular momentum J together
-- with source/probe geometry.  Microscopic subdivision into N constituents is
-- not itself an enhancement parameter.
------------------------------------------------------------------------

record FarFieldKernel : Set where
  constructor far-field-kernel
  field
    weakField : Bool
    stationarySource : Bool
    compactRelativeToProbeDistance : Bool
    linearSuperposition : Bool
    fieldScaling : String
    angularMomentumScaling : String

canonicalFarFieldKernel : FarFieldKernel
canonicalFarFieldKernel = far-field-kernel
  true true true true
  "|Bg| ~ kappa_G * G * |J| / (c^2 r^3)"
  "J_total = sum_i L_i = integral r cross J_m dV"

------------------------------------------------------------------------
-- Geometry/orientation factors.
--
-- Gamma_geometry captures source-position/probe-distance weighting.
-- Gamma_orientation captures vector projection/cancellation.
------------------------------------------------------------------------

record GeometryFactorization : Set where
  constructor geometry-factorization
  field
    naiveScalarEstimate : String
    resolvedVectorEstimate : String
    geometryFactor : String
    orientationFactor : String
    constitutiveFactor : String

canonicalGeometryFactorization : GeometryFactorization
canonicalGeometryFactorization = geometry-factorization
  "B_claim = N * B_ion"
  "B_bulk(xobs) = sum_i K(xobs,xi,Li)"
  "Gamma_geometry(xobs,{xi})"
  "Gamma_orientation({Li},xobs)"
  "Gamma_constitutive"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

record GeometryBoundary : Set where
  constructor geometry-boundary
  field
    fixedNDeterminesExternalField : Bool
    fixedNDeterminesExternalFieldIsFalse : fixedNDeterminesExternalField ≡ false

    fixedTotalAngularMomentumDeterminesNearFieldEverywhere : Bool
    fixedTotalAngularMomentumDeterminesNearFieldEverywhereIsFalse :
      fixedTotalAngularMomentumDeterminesNearFieldEverywhere ≡ false

    fixedTotalAngularMomentumDeterminesLeadingFarFieldDipoleScaling : Bool
    fixedTotalAngularMomentumDeterminesLeadingFarFieldDipoleScalingIsTrue :
      fixedTotalAngularMomentumDeterminesLeadingFarFieldDipoleScaling ≡ true

    coherenceImpliesUnitGeometryFactor : Bool
    coherenceImpliesUnitGeometryFactorIsFalse :
      coherenceImpliesUnitGeometryFactor ≡ false

    coherenceImpliesUnitOrientationFactor : Bool
    coherenceImpliesUnitOrientationFactorIsFalse :
      coherenceImpliesUnitOrientationFactor ≡ false

canonicalGeometryBoundary : GeometryBoundary
canonicalGeometryBoundary = geometry-boundary
  false refl
  false refl
  true refl
  false refl
  false refl

------------------------------------------------------------------------
-- BIDI acquisition path for converting the historical N-fold estimate into a
-- geometry-resolved field prediction.
------------------------------------------------------------------------

data GeometryFactorLeaf : Set where
  sourceDensityLeaf : GeometryFactorLeaf
  sourceSupportLeaf : GeometryFactorLeaf
  angularMomentumDensityLeaf : GeometryFactorLeaf
  probeCoordinateLeaf : GeometryFactorLeaf
  kernelRegimeLeaf : GeometryFactorLeaf
  vectorIntegralLeaf : GeometryFactorLeaf
  geometryFactorClosed : GeometryFactorLeaf

record GeometryFactorState : Set where
  constructor geometry-factor-state
  field
    sourceDensityOwned : Bool
    sourceSupportOwned : Bool
    angularMomentumDensityOwned : Bool
    probeCoordinateOwned : Bool
    kernelRegimeOwned : Bool
    vectorIntegralOwned : Bool

firstOpenGeometryFactorLeaf : GeometryFactorState → GeometryFactorLeaf
firstOpenGeometryFactorLeaf (geometry-factor-state false s a p k v) = sourceDensityLeaf
firstOpenGeometryFactorLeaf (geometry-factor-state true false a p k v) = sourceSupportLeaf
firstOpenGeometryFactorLeaf (geometry-factor-state true true false p k v) = angularMomentumDensityLeaf
firstOpenGeometryFactorLeaf (geometry-factor-state true true true false k v) = probeCoordinateLeaf
firstOpenGeometryFactorLeaf (geometry-factor-state true true true true false v) = kernelRegimeLeaf
firstOpenGeometryFactorLeaf (geometry-factor-state true true true true true false) = vectorIntegralLeaf
firstOpenGeometryFactorLeaf (geometry-factor-state true true true true true true) = geometryFactorClosed

currentIdealizedGeometryFrontier : GeometryFactorState
currentIdealizedGeometryFrontier = geometry-factor-state false false false false true false

currentFirstOpenGeometryFactorLeaf : GeometryFactorLeaf
currentFirstOpenGeometryFactorLeaf = firstOpenGeometryFactorLeaf currentIdealizedGeometryFrontier

------------------------------------------------------------------------
-- Same-J comparison theorem shape.
--
-- If two source models share total J and are both compact relative to the
-- probe distance, their leading far-field gravitomagnetic dipole scaling is
-- the same up to the convention/angular factor.  This does NOT imply their
-- near fields are identical.
------------------------------------------------------------------------

record SameJFarFieldWeld : Set where
  constructor same-j-far-field-weld
  field
    sameTotalAngularMomentum : Bool
    bothFarField : Bool
    leadingDipoleScalingMatches : Bool
    nearFieldProfilesNeedNotMatch : Bool
    nearFieldProfilesNeedNotMatchIsTrue : nearFieldProfilesNeedNotMatch ≡ true

canonicalSameJFarFieldWeld : SameJFarFieldWeld
canonicalSameJFarFieldWeld = same-j-far-field-weld true true true true refl
