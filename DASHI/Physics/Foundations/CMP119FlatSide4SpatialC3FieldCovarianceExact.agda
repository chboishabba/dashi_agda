{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119FlatSide4SpatialC3FieldCovarianceExact where

------------------------------------------------------------------------
-- LITERAL SIDE-4 SU(2) FIELD REALISATION OF THE SPATIAL C3 STRESS ACTION
--
-- The classical curvature C3 theorem is already exact on CurvatureSix.  This
-- file pushes it down to the actual side-four positive-bond field used by the
-- flat Wilson/Hodge lane.  No abstract field action is supplied by a caller:
-- spatial C3 is the literal pullback of the existing (site,axis) bond carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119ClassicalCurvatureTenMetricVariationExact as Metric
import DASHI.Physics.Foundations.CMP119FlatSide4CurvatureStressExact as FlatStress
import DASHI.Physics.Foundations.CMP119ClassicalCurvatureSpatialC3CovarianceExact as ClassicalC3
import DASHI.Physics.Foundations.BalabanR144SpatialC3StressRestrictionExact as Spatial
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatWilsonCurlIdentificationExact as Flat
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlScalarExact as Curl

------------------------------------------------------------------------
-- Spatial 1->2->3->1 on axes and sites, with explicit inverses.
------------------------------------------------------------------------

spatialC3Axis : Torus.Axis4 → Torus.Axis4
spatialC3Axis Hodge.axis0 = Hodge.axis0
spatialC3Axis Hodge.axis1 = Hodge.axis2
spatialC3Axis Hodge.axis2 = Hodge.axis3
spatialC3Axis Hodge.axis3 = Hodge.axis1

inverseSpatialC3Axis : Torus.Axis4 → Torus.Axis4
inverseSpatialC3Axis Hodge.axis0 = Hodge.axis0
inverseSpatialC3Axis Hodge.axis1 = Hodge.axis3
inverseSpatialC3Axis Hodge.axis2 = Hodge.axis1
inverseSpatialC3Axis Hodge.axis3 = Hodge.axis2

inverseSpatialC3AxisAfter : ∀ axis →
  inverseSpatialC3Axis (spatialC3Axis axis) ≡ axis
inverseSpatialC3AxisAfter Hodge.axis0 = refl
inverseSpatialC3AxisAfter Hodge.axis1 = refl
inverseSpatialC3AxisAfter Hodge.axis2 = refl
inverseSpatialC3AxisAfter Hodge.axis3 = refl

spatialC3Site : Hodge.Site4 → Hodge.Site4
spatialC3Site
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) =
  Torus.pair (Torus.pair x0 x3) (Torus.pair x1 x2)

inverseSpatialC3Site : Hodge.Site4 → Hodge.Site4
inverseSpatialC3Site
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) =
  Torus.pair (Torus.pair x0 x2) (Torus.pair x3 x1)

inverseSpatialC3SiteAfter : ∀ site →
  inverseSpatialC3Site (spatialC3Site site) ≡ site
inverseSpatialC3SiteAfter
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl

spatialC3SiteAfterInverse : ∀ site →
  spatialC3Site (inverseSpatialC3Site site) ≡ site
spatialC3SiteAfterInverse
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl

inverseSiteCommutesWithForwardShift : ∀ axis site →
  inverseSpatialC3Site
    (Hodge.shiftForward (spatialC3Axis axis) (spatialC3Site site))
  ≡ Hodge.shiftForward axis site
inverseSiteCommutesWithForwardShift Hodge.axis0
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
inverseSiteCommutesWithForwardShift Hodge.axis1
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
inverseSiteCommutesWithForwardShift Hodge.axis2
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
inverseSiteCommutesWithForwardShift Hodge.axis3
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl

------------------------------------------------------------------------
-- Literal pullback action on the actual physical side-4 bond field.
------------------------------------------------------------------------

spatialC3PhysicalField :
  Physical.PhysicalSU2BondField4 → Physical.PhysicalSU2BondField4
spatialC3PhysicalField field coordinate (Torus.pair site axis) =
  field coordinate
    (Torus.pair
      (inverseSpatialC3Site site)
      (inverseSpatialC3Axis axis))

spatialC3FieldAtImage : ∀ field coordinate site axis →
  spatialC3PhysicalField field coordinate
    (Torus.pair (spatialC3Site site) (spatialC3Axis axis))
  ≡ field coordinate (Torus.pair site axis)
spatialC3FieldAtImage field coordinate site axis
  rewrite inverseSpatialC3SiteAfter site
        | inverseSpatialC3AxisAfter axis = refl

------------------------------------------------------------------------
-- Curl naturality.  The finite side-four proof is definitionally exhaustive.
------------------------------------------------------------------------

spatialC3PlaquetteCurlCoordinate :
  ∀ field coordinate left right site →
  Flat.plaquetteCurlCoordinate
    (spatialC3PhysicalField field)
    coordinate
    (spatialC3Axis left)
    (spatialC3Axis right)
    (spatialC3Site site)
  ≡ Flat.plaquetteCurlCoordinate field coordinate left right site
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis0 Hodge.axis0
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis0 Hodge.axis1
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis0 Hodge.axis2
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis0 Hodge.axis3
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis1 Hodge.axis0
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis1 Hodge.axis1
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis1 Hodge.axis2
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis1 Hodge.axis3
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis2 Hodge.axis0
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis2 Hodge.axis1
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis2 Hodge.axis2
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis2 Hodge.axis3
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis3 Hodge.axis0
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis3 Hodge.axis1
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis3 Hodge.axis2
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3PlaquetteCurlCoordinate field coordinate Hodge.axis3 Hodge.axis3
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl

plaquetteCurlCoordinateAntisymmetric :
  ∀ field coordinate left right site →
  Flat.plaquetteCurlCoordinate field coordinate right left site
  ≡ - Flat.plaquetteCurlCoordinate field coordinate left right site
plaquetteCurlCoordinateAntisymmetric field coordinate left right site =
  ℚRing.solve-∀
    (Hodge.forwardDifference right
      (Flat.asPeriodicPhysicalField field coordinate left) site)
    (Hodge.forwardDifference left
      (Flat.asPeriodicPhysicalField field coordinate right) site)

vec3Cong : ∀ {ax ay az bx by bz} →
  ax ≡ bx → ay ≡ by → az ≡ bz →
  Curl.vec3 ax ay az ≡ Curl.vec3 bx by bz
vec3Cong refl refl refl = refl

localCurvatureVectorSpatialC3 : ∀ field left right site →
  FlatStress.localCurvatureVector
    (spatialC3PhysicalField field)
    (spatialC3Axis left)
    (spatialC3Axis right)
    (spatialC3Site site)
  ≡ FlatStress.localCurvatureVector field left right site
localCurvatureVectorSpatialC3 field left right site =
  vec3Cong
    (spatialC3PlaquetteCurlCoordinate
      field Physical.coordinateX left right site)
    (spatialC3PlaquetteCurlCoordinate
      field Physical.coordinateY left right site)
    (spatialC3PlaquetteCurlCoordinate
      field Physical.coordinateZ left right site)

localCurvatureVectorAntisymmetric : ∀ field left right site →
  FlatStress.localCurvatureVector field right left site
  ≡ Curl.negV (FlatStress.localCurvatureVector field left right site)
localCurvatureVectorAntisymmetric field left right site =
  vec3Cong
    (plaquetteCurlCoordinateAntisymmetric
      field Physical.coordinateX left right site)
    (plaquetteCurlCoordinateAntisymmetric
      field Physical.coordinateY left right site)
    (plaquetteCurlCoordinateAntisymmetric
      field Physical.coordinateZ left right site)

------------------------------------------------------------------------
-- The six stored curvature slots are exactly the two-form C3 action.
------------------------------------------------------------------------

rotatedF01 : ∀ field site →
  Metric.f01
    (FlatStress.localCurvatureSix
      (spatialC3PhysicalField field) (spatialC3Site site))
  ≡ Metric.f03 (FlatStress.localCurvatureSix field site)
rotatedF01 field site =
  localCurvatureVectorSpatialC3 field Hodge.axis0 Hodge.axis3 site

rotatedF02 : ∀ field site →
  Metric.f02
    (FlatStress.localCurvatureSix
      (spatialC3PhysicalField field) (spatialC3Site site))
  ≡ Metric.f01 (FlatStress.localCurvatureSix field site)
rotatedF02 field site =
  localCurvatureVectorSpatialC3 field Hodge.axis0 Hodge.axis1 site

rotatedF03 : ∀ field site →
  Metric.f03
    (FlatStress.localCurvatureSix
      (spatialC3PhysicalField field) (spatialC3Site site))
  ≡ Metric.f02 (FlatStress.localCurvatureSix field site)
rotatedF03 field site =
  localCurvatureVectorSpatialC3 field Hodge.axis0 Hodge.axis2 site

rotatedF12 : ∀ field site →
  Metric.f12
    (FlatStress.localCurvatureSix
      (spatialC3PhysicalField field) (spatialC3Site site))
  ≡ Curl.negV (Metric.f13 (FlatStress.localCurvatureSix field site))
rotatedF12 field site =
  trans
    (localCurvatureVectorSpatialC3 field Hodge.axis3 Hodge.axis1 site)
    (localCurvatureVectorAntisymmetric field Hodge.axis1 Hodge.axis3 site)

rotatedF13 : ∀ field site →
  Metric.f13
    (FlatStress.localCurvatureSix
      (spatialC3PhysicalField field) (spatialC3Site site))
  ≡ Curl.negV (Metric.f23 (FlatStress.localCurvatureSix field site))
rotatedF13 field site =
  trans
    (localCurvatureVectorSpatialC3 field Hodge.axis3 Hodge.axis2 site)
    (localCurvatureVectorAntisymmetric field Hodge.axis2 Hodge.axis3 site)

rotatedF23 : ∀ field site →
  Metric.f23
    (FlatStress.localCurvatureSix
      (spatialC3PhysicalField field) (spatialC3Site site))
  ≡ Metric.f12 (FlatStress.localCurvatureSix field site)
rotatedF23 field site =
  localCurvatureVectorSpatialC3 field Hodge.axis1 Hodge.axis2 site

------------------------------------------------------------------------
-- Therefore the literal side-four local stress obeys the same spatial C3 law.
------------------------------------------------------------------------

literalLocalStressSpatialC3Covariant :
  ∀ field site component →
  FlatStress.localStressInsertion
    (spatialC3PhysicalField field)
    (spatialC3Site site)
    (Spatial.spatialXYZComponent component)
  ≡ FlatStress.localStressInsertion field site component
literalLocalStressSpatialC3Covariant field site component
  rewrite rotatedF01 field site
        | rotatedF02 field site
        | rotatedF03 field site
        | rotatedF12 field site
        | rotatedF13 field site
        | rotatedF23 field site =
  ClassicalC3.spatialC3StressCovariant
    (FlatStress.localCurvatureSix field site) component

------------------------------------------------------------------------
-- Frontier accounting.
------------------------------------------------------------------------

literalSide4FieldSpatialC3Recovered : Bool
literalSide4FieldSpatialC3Recovered = true

literalSide4CurlSpatialC3Recovered : Bool
literalSide4CurlSpatialC3Recovered = true

literalSide4StressSpatialC3Recovered : Bool
literalSide4StressSpatialC3Recovered = true

literalSide4StressUsesSameR144SpatialTensorAction : Bool
literalSide4StressUsesSameR144SpatialTensorAction = true

-- This is a literal flat/tangent side-four physical field theorem.  It does not
-- identify the selected nonlinear CMP109/116 generated-action background with
-- this flat field, so the full generated-action Q1 source curve remains open.
literalSide4FieldC3ClosesFullGeneratedActionQ1 : Bool
literalSide4FieldC3ClosesFullGeneratedActionQ1 = false
