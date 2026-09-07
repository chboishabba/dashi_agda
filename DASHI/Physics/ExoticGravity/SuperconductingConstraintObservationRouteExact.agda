module DASHI.Physics.ExoticGravity.SuperconductingConstraintObservationRouteExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentalConstraintRegistryExact as Registry
import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs

------------------------------------------------------------------------
-- LEGACY CONSTRAINT MEASURED-CHANNEL -> TYPED ROUTE
--
-- The registry predates the typed GR observation BIDI and stores measuredChannel
-- as String.  This adapter classifies only what the current registry description
-- supports.  The classification is DASHI reconstruction, not a source quotation
-- and not a calibrated GravitationalObservationReceipt.
------------------------------------------------------------------------

data ConstraintObservationRoute : Set where
  typedGravityConstraint : Obs.GravitationalObservationChannel → ConstraintObservationRoute
  compositeAngularSensorConstraint : ConstraintObservationRoute
  constraintChannelUnresolved : ConstraintObservationRoute

record ConstraintObservationRouteReceipt : Set where
  constructor constraint-observation-route-receipt
  field
    constraint : Registry.ExperimentalConstraint
    legacyMeasuredChannel : String
    legacyMeasuredChannelMatches :
      Registry.measuredChannel constraint ≡ legacyMeasuredChannel
    route : ConstraintObservationRoute
    reconstructionScope : String

open ConstraintObservationRouteReceipt public

nasaStaticYBCORoute : ConstraintObservationRouteReceipt
nasaStaticYBCORoute = constraint-observation-route-receipt
  Registry.nasaStaticYBCO
  (Registry.measuredChannel Registry.nasaStaticYBCO)
  refl
  (typedGravityConstraint Obs.staticLoadOrWeight)
  "DASHI reconstruction from the registry's apparent-weight/gravity-response description into the static-load/weight observation family"

nasaRFArtifactRoute : ConstraintObservationRouteReceipt
nasaRFArtifactRoute = constraint-observation-route-receipt
  Registry.nasaRFArrtifact
  (Registry.measuredChannel Registry.nasaRFArrtifact)
  refl
  (typedGravityConstraint Obs.staticLoadOrWeight)
  "DASHI reconstruction from the precision-balance/proposed-gravity-response description into the static-load/weight observation family"

hathawayReplicationRoute : ConstraintObservationRouteReceipt
hathawayReplicationRoute = constraint-observation-route-receipt
  Registry.hathawayReplication
  (Registry.measuredChannel Registry.hathawayReplication)
  refl
  (typedGravityConstraint Obs.staticLoadOrWeight)
  "DASHI reconstruction from the published weight/gravity-modification-above-apparatus description into the static-load/weight observation family"

tajmarTransitionMismatchRoute : ConstraintObservationRouteReceipt
tajmarTransitionMismatchRoute = constraint-observation-route-receipt
  Registry.tajmarTransitionMismatch
  (Registry.measuredChannel Registry.tajmarTransitionMismatch)
  refl
  compositeAngularSensorConstraint
  "accelerometer plus laser-gyroscope angular-response channel is retained as a composite sensor result rather than coerced into linear local gravitational acceleration"

tajmarLargeTheoryBoundRoute : ConstraintObservationRouteReceipt
tajmarLargeTheoryBoundRoute = constraint-observation-route-receipt
  Registry.tajmarLargeTheoryBound
  (Registry.measuredChannel Registry.tajmarLargeTheoryBound)
  refl
  compositeAngularSensorConstraint
  "frame-dragging-like angular response is retained as a composite angular-sensor constraint rather than coerced into a current GR observation channel"

------------------------------------------------------------------------
-- Introspective non-collapse.
------------------------------------------------------------------------

staticWeightAndAngularConstraintRoutesDistinct :
  route hathawayReplicationRoute ≡ route tajmarTransitionMismatchRoute → ⊥
staticWeightAndAngularConstraintRoutesDistinct ()

record ConstraintObservationRouteBoundary : Set where
  constructor constraint-observation-route-boundary
  field
    legacyMeasuredChannelStringIsTypedObservation : Bool
    weightBalanceConstraintsMayRefineStaticLoadLane : Bool
    angularSensorConstraintEqualsStaticWeightLane : Bool
    angularSensorConstraintEqualsFreeFallLane : Bool
    routeClassificationIsSourceEntitledStatement : Bool
    typedRouteAutomaticallyCreatesCalibratedObservationReceipt : Bool
    nullConstraintAutomaticallyProvesUniversalNoCoupling : Bool

canonicalConstraintObservationRouteBoundary : ConstraintObservationRouteBoundary
canonicalConstraintObservationRouteBoundary =
  constraint-observation-route-boundary
    false true false false false false false
