module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCOMGeometryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Geometry.RigidMotionSemidirectProductExact as SE3
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact as Config
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceAtomSelectionExact as Selection
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSIQuantityBridgeExact as SIAdK
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- MASS-WEIGHTED CENTER-OF-MASS GEOMETRY
--
-- This owner is deliberately model-parametric at the arithmetic/trigonometric
-- layer.  The current repo has exact fixed-point SI quantities but no canonical
-- exact real/acos implementation.  We therefore expose the exact geometric
-- obligations and prove the rigid-motion consequences from them, rather than
-- smuggling floating-point or an unproved transcendental operation into Agda.
------------------------------------------------------------------------

record AdKCOMGeometryModel (rigidModel : SE3.RigidMotionModel) : Set₁ where
  constructor adk-com-geometry-model
  field
    massOf : Config.AtomSiteIdentity → Nat
    massConventionReference : String
    selectionResolutionReference : String

    centerOfMass :
      Config.AtomisticConfiguration →
      Selection.AtomSelectionSpec →
      Config.CartesianCoordinate

    centerOfMassMassWeighted :
      (configuration : Config.AtomisticConfiguration) →
      (selection : Selection.AtomSelectionSpec) →
      Set

    angleDegrees :
      Config.CartesianCoordinate →
      Config.CartesianCoordinate →
      Config.CartesianCoordinate →
      Nat

    distance :
      Config.CartesianCoordinate →
      Config.CartesianCoordinate →
      SI.Quantity SI.Length SIAdK.angstromScale

    transformConfiguration :
      SE3.RigidMotion rigidModel →
      Config.AtomisticConfiguration →
      Config.AtomisticConfiguration

    transformPoint :
      SE3.RigidMotion rigidModel →
      Config.CartesianCoordinate →
      Config.CartesianCoordinate

    centerOfMassEquivariant :
      (g : SE3.RigidMotion rigidModel) →
      (configuration : Config.AtomisticConfiguration) →
      (selection : Selection.AtomSelectionSpec) →
      centerOfMass (transformConfiguration g configuration) selection
      ≡ transformPoint g (centerOfMass configuration selection)

    angleRigidInvariant :
      (g : SE3.RigidMotion rigidModel) →
      (a b c : Config.CartesianCoordinate) →
      angleDegrees (transformPoint g a) (transformPoint g b) (transformPoint g c)
      ≡ angleDegrees a b c

    distanceRigidInvariant :
      (g : SE3.RigidMotion rigidModel) →
      (a b : Config.CartesianCoordinate) →
      distance (transformPoint g a) (transformPoint g b)
      ≡ distance a b

open AdKCOMGeometryModel public

------------------------------------------------------------------------
-- Derived COM angle/distance evaluators.
------------------------------------------------------------------------

angleOfThreeCOMs :
  {rigidModel : SE3.RigidMotionModel} →
  AdKCOMGeometryModel rigidModel →
  Config.AtomisticConfiguration →
  Selection.AtomSelectionSpec →
  Selection.AtomSelectionSpec →
  Selection.AtomSelectionSpec →
  Nat
angleOfThreeCOMs geometry configuration first vertex third =
  angleDegrees geometry
    (centerOfMass geometry configuration first)
    (centerOfMass geometry configuration vertex)
    (centerOfMass geometry configuration third)

distanceOfTwoCOMs :
  {rigidModel : SE3.RigidMotionModel} →
  AdKCOMGeometryModel rigidModel →
  Config.AtomisticConfiguration →
  Selection.AtomSelectionSpec →
  Selection.AtomSelectionSpec →
  SI.Quantity SI.Length SIAdK.angstromScale
distanceOfTwoCOMs geometry configuration first second =
  distance geometry
    (centerOfMass geometry configuration first)
    (centerOfMass geometry configuration second)

------------------------------------------------------------------------
-- Rigid-motion invariance theorems.
------------------------------------------------------------------------

angleOfThreeCOMsRigidInvariant :
  {rigidModel : SE3.RigidMotionModel} →
  (geometry : AdKCOMGeometryModel rigidModel) →
  (g : SE3.RigidMotion rigidModel) →
  (configuration : Config.AtomisticConfiguration) →
  (first vertex third : Selection.AtomSelectionSpec) →
  angleOfThreeCOMs geometry
    (transformConfiguration geometry g configuration)
    first vertex third
  ≡ angleOfThreeCOMs geometry configuration first vertex third
angleOfThreeCOMsRigidInvariant geometry g configuration first vertex third
  rewrite centerOfMassEquivariant geometry g configuration first
        | centerOfMassEquivariant geometry g configuration vertex
        | centerOfMassEquivariant geometry g configuration third =
  angleRigidInvariant geometry g
    (centerOfMass geometry configuration first)
    (centerOfMass geometry configuration vertex)
    (centerOfMass geometry configuration third)

distanceOfTwoCOMsRigidInvariant :
  {rigidModel : SE3.RigidMotionModel} →
  (geometry : AdKCOMGeometryModel rigidModel) →
  (g : SE3.RigidMotion rigidModel) →
  (configuration : Config.AtomisticConfiguration) →
  (first second : Selection.AtomSelectionSpec) →
  distanceOfTwoCOMs geometry
    (transformConfiguration geometry g configuration)
    first second
  ≡ distanceOfTwoCOMs geometry configuration first second
distanceOfTwoCOMsRigidInvariant geometry g configuration first second
  rewrite centerOfMassEquivariant geometry g configuration first
        | centerOfMassEquivariant geometry g configuration second =
  distanceRigidInvariant geometry g
    (centerOfMass geometry configuration first)
    (centerOfMass geometry configuration second)

------------------------------------------------------------------------
-- The mass source is an input to geometry, never a coordinate generator.
------------------------------------------------------------------------

atomicMassConvention : Config.AtomicMassConvention
atomicMassConvention = Config.canonicalAtomicMassConvention

massWeightingReading : String
massWeightingReading =
  "COM weighting consumes the explicitly attributed atomic-mass convention; atom identity, mass convention and 3-D coordinate remain separate coordinates"

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data AtomicMassSourceCreatesCoordinate : Set where
data COMGeometryCreatesForceField : Set where
data RigidMotionInvarianceCreatesDynamics : Set where
data ExactFixedPointCoordinatesCreateExactAcos : Set where

atomicMassSourceDoesNotCreateCoordinate : AtomicMassSourceCreatesCoordinate → ⊥
atomicMassSourceDoesNotCreateCoordinate ()

comGeometryDoesNotCreateForceField : COMGeometryCreatesForceField → ⊥
comGeometryDoesNotCreateForceField ()

rigidMotionInvarianceDoesNotCreateDynamics : RigidMotionInvarianceCreatesDynamics → ⊥
rigidMotionInvarianceDoesNotCreateDynamics ()

fixedPointCoordinatesDoNotCreateExactAcos : ExactFixedPointCoordinatesCreateExactAcos → ⊥
fixedPointCoordinatesDoNotCreateExactAcos ()

record AdKCOMGeometryBoundary : Set where
  constructor adk-com-geometry-boundary
  field
    massWeightedCenterOfMassExplicit : Bool
    massConventionAttributed : Bool
    distanceAndAngleGeometrySeparated : Bool
    globalTranslationInvariant : Bool
    globalRotationInvariant : Bool
    reusesCanonicalSE3Carrier : Bool
    exactAcosImplementationPaidHere : Bool
    atomicMassSourceCreatesCoordinate : Bool
    comGeometryCreatesForceField : Bool
    rigidMotionInvarianceCreatesDynamics : Bool
open AdKCOMGeometryBoundary public

canonicalAdKCOMGeometryBoundary : AdKCOMGeometryBoundary
canonicalAdKCOMGeometryBoundary =
  adk-com-geometry-boundary
    true true true true true true false
    false false false
