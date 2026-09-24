module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCOMGeometryValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCOMGeometryExact as Geometry

boundary = Geometry.canonicalAdKCOMGeometryBoundary

_ : Geometry.massWeightedCenterOfMassExplicit boundary ≡ true
_ = refl

_ : Geometry.distanceAndAngleGeometrySeparated boundary ≡ true
_ = refl

_ : Geometry.globalTranslationInvariant boundary ≡ true
_ = refl

_ : Geometry.globalRotationInvariant boundary ≡ true
_ = refl

_ : Geometry.atomicMassSourceCreatesCoordinate boundary ≡ false
_ = refl

_ : Geometry.comGeometryCreatesForceField boundary ≡ false
_ = refl
