module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGOrderParameterIdentityWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.SuperconductingTransitionOrderParameterLockBidiExact as Transition
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScalingModelDiscriminatorExact as Scaling

------------------------------------------------------------------------
-- ORDER-PARAMETER SAME-OBJECT WELD
--
-- Transition lock and scaling-model separation both require an order-parameter
-- measurement.  They must consume the same carrier/revision if one experiment
-- is meant to pay both residuals.  Merely saying "order parameter measured"
-- twice is not a same-object receipt.
------------------------------------------------------------------------

record OrderParameterMeasurementIdentity : Set where
  constructor order-parameter-measurement-identity
  field
    carrier : String
    revision : String
    observableIdentity : String

open OrderParameterMeasurementIdentity public

record TransitionScalingOrderParameterWeld
    (transition : Transition.TransitionOrderParameterLockReceipt)
    (scaling : Scaling.ScalingModelSeparationReceipt) : Set₁ where
  constructor transition-scaling-order-parameter-weld
  field
    transitionMeasurementIdentity : OrderParameterMeasurementIdentity
    scalingMeasurementIdentity : OrderParameterMeasurementIdentity

    sameCarrier :
      carrier transitionMeasurementIdentity
        ≡ carrier scalingMeasurementIdentity
    sameRevision :
      revision transitionMeasurementIdentity
        ≡ revision scalingMeasurementIdentity
    sameObservable :
      observableIdentity transitionMeasurementIdentity
        ≡ observableIdentity scalingMeasurementIdentity

    TransitionReceiptDerivation : Set
    transitionReceiptDerivation : TransitionReceiptDerivation

    ScalingReceiptDerivation : Set
    scalingReceiptDerivation : ScalingReceiptDerivation

open TransitionScalingOrderParameterWeld public

------------------------------------------------------------------------
-- Introspective collision: two coarse "order parameter measured" surfaces may
-- refer to different data carriers and therefore cannot be merged by label.
------------------------------------------------------------------------

data OrderParameterFixture : Set where
  transitionCarrierFixture scalingCarrierFixture : OrderParameterFixture

data CoarseMeasurementSurface : Set where
  orderParameterMeasured : CoarseMeasurementSurface

coarseObserve : OrderParameterFixture → CoarseMeasurementSurface
coarseObserve _ = orderParameterMeasured

measurementCarrierTag : OrderParameterFixture → String
measurementCarrierTag transitionCarrierFixture = "transition-run/order-parameter"
measurementCarrierTag scalingCarrierFixture = "scaling-run/order-parameter"

coarseCollision :
  coarseObserve transitionCarrierFixture ≡ coarseObserve scalingCarrierFixture
coarseCollision = refl

data SameOrderParameterCarrierPermission : Set where

coarseLabelDoesNotCreateSameCarrierReceipt :
  SameOrderParameterCarrierPermission → ⊥
coarseLabelDoesNotCreateSameCarrierReceipt ()

record OrderParameterIdentityBoundary : Set where
  constructor order-parameter-identity-boundary
  field
    twoOrderParameterLabelsAutomaticallyMeanSameMeasurement : Bool
    exactCarrierIdentityRequired : Bool
    exactRevisionIdentityRequired : Bool
    exactObservableIdentityRequired : Bool
    transitionLockAlonePaysScalingModelSeparation : Bool
    scalingModelSeparationAlonePaysTransitionLock : Bool
    sameObjectWeldAutomaticallyProvesNegativeEffectiveG : Bool

canonicalOrderParameterIdentityBoundary : OrderParameterIdentityBoundary
canonicalOrderParameterIdentityBoundary =
  order-parameter-identity-boundary false true true true false false false
