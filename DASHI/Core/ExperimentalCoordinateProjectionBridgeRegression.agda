module DASHI.Core.ExperimentalCoordinateProjectionBridgeRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ExperimentalCoordinateDesignExact as Coordinate
import DASHI.Core.CoarseFineFabricCalculusExact as Calculus
import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as Join
import DASHI.Core.ExperimentalCoordinateProjectionBridgeExact as Bridge

record World : Set where
  constructor world
  field visible : Bool
        hidden : Bool
open World public

data Control : Set where noop : Control
data Dimension : Set where informational : Dimension

data CoordinateKey : Set where hiddenKey : CoordinateKey

design : Coordinate.ExperimentalCoordinateDesign World Control Bool Dimension
design = record
  { Coordinate = CoordinateKey
  ; role = λ key → Coordinate.measuredObservable
  ; dimension = λ key → informational
  ; read = λ key state → hidden state
  ; applyControl = λ control state → state
  ; coordinateReference = λ key → "hidden"
  ; dimensionReference = λ key → "informational"
  ; calibrationOrDerivationReference = λ key → "fixture"
  ; controlReference = λ control → "noop"
  }

coarse : World → Bool
coarse = visible

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

separation : Coordinate.CoordinateSeparatesCollision design coarse
separation = Coordinate.coordinateSeparatesCollision
  hiddenKey
  (world false true)
  (world false false)
  refl
  trueNotFalse

collision :
  Calculus.ProjectionCollision coarse (Coordinate.read design hiddenKey)
collision = Bridge.coordinateSeparationYieldsProjectionCollision separation

joinedObserver : World → Bool × Bool
joinedObserver = Join.jointAxis coarse (Coordinate.read design hiddenKey)

joinedObserverRetainsBothAxes :
  Join.RetainsBothRequiredAxes
    joinedObserver
    coarse
    (Coordinate.read design hiddenKey)
joinedObserverRetainsBothAxes =
  Bridge.coordinateJoinRetainsExistingAndNewAxis separation

joinedObserverRetainsExisting :
  Join.RetainsAxis joinedObserver coarse
joinedObserverRetainsExisting =
  Join.retainsLeft joinedObserverRetainsBothAxes

joinedObserverRetainsNewCoordinate :
  Join.RetainsAxis joinedObserver (Coordinate.read design hiddenKey)
joinedObserverRetainsNewCoordinate =
  Join.retainsRight joinedObserverRetainsBothAxes

bridgeDoesNotCreatePhysicalDimension : Bool
bridgeDoesNotCreatePhysicalDimension =
  Bridge.ExperimentalCoordinateProjectionBoundary.coordinateSeparationCreatesPhysicalDimension
    Bridge.canonicalExperimentalCoordinateProjectionBoundary

bridgeDoesNotCreatePhysicalDimensionIsFalse :
  bridgeDoesNotCreatePhysicalDimension ≡ false
bridgeDoesNotCreatePhysicalDimensionIsFalse = refl
