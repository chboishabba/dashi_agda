module DASHI.Physics.Foundations.PrecisionThrustClosureExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Foundations.PhysicalResidualPromotionExact as Promotion

------------------------------------------------------------------------
-- PRECISION-THRUST NUISANCE CLOSURE
--
-- The nuisance list is explicit and the closure witness is indexed by the
-- exact residual candidate.  A surviving candidate still does not become a
-- gravity claim without an independent gravity/metric consumer.
------------------------------------------------------------------------

data PrecisionNuisanceChannel : Set where
  thermalExpansionOrStrain : PrecisionNuisanceChannel
  pressureOrBuoyancy : PrecisionNuisanceChannel
  outgassing : PrecisionNuisanceChannel
  vibration : PrecisionNuisanceChannel
  supportsOrCables : PrecisionNuisanceChannel
  electrostaticCoupling : PrecisionNuisanceChannel
  magneticOrLorentzCoupling : PrecisionNuisanceChannel
  radiationPressure : PrecisionNuisanceChannel
  convection : PrecisionNuisanceChannel
  facilityCoupling : PrecisionNuisanceChannel
  sensorDrift : PrecisionNuisanceChannel

declaredNuisanceChannels : List PrecisionNuisanceChannel
declaredNuisanceChannels =
  thermalExpansionOrStrain ∷
  pressureOrBuoyancy ∷
  outgassing ∷
  vibration ∷
  supportsOrCables ∷
  electrostaticCoupling ∷
  magneticOrLorentzCoupling ∷
  radiationPressure ∷
  convection ∷
  facilityCoupling ∷
  sensorDrift ∷ []

record PrecisionThrustClosureObligation : Set where
  constructor precision-thrust-closure-obligation
  field
    candidate : Promotion.AnomalousMomentumCandidate
    nuisanceSetReference : String
    allDeclaredNuisanceChannelsClosed : Bool
    sameObjectCalibrationPaid : Bool
    predictiveScalingPaid : Bool
    apparatusChangePaid : Bool
    independentReplicationPaid : Bool
    independentGravityConsumerPaid : Bool

open PrecisionThrustClosureObligation public

canonicalPrecisionThrustClosureObligation : PrecisionThrustClosureObligation
canonicalPrecisionThrustClosureObligation =
  precision-thrust-closure-obligation
    Promotion.canonicalAnomalousMomentumCandidate
    "thermal, pressure/buoyancy, outgassing, vibration, supports/cables, electrostatic, magnetic/Lorentz, radiation pressure, convection, facility and sensor channels"
    false false false false false false

record PrecisionThrustClosureWitness
    (obligation : PrecisionThrustClosureObligation) : Set where
  constructor precision-thrust-closure-witness
  field
    allDeclaredNuisanceChannelsClosedIsTrue :
      allDeclaredNuisanceChannelsClosed obligation ≡ true
    sameObjectCalibrationPaidIsTrue :
      sameObjectCalibrationPaid obligation ≡ true
    predictiveScalingPaidIsTrue :
      predictiveScalingPaid obligation ≡ true
    apparatusChangePaidIsTrue :
      apparatusChangePaid obligation ≡ true
    independentReplicationPaidIsTrue :
      independentReplicationPaid obligation ≡ true

open PrecisionThrustClosureWitness public

record PrecisionGravityInterpretationWitness
    (obligation : PrecisionThrustClosureObligation) : Set where
  constructor precision-gravity-interpretation-witness
  field
    residualClosure : PrecisionThrustClosureWitness obligation
    independentGravityConsumerPaidIsTrue :
      independentGravityConsumerPaid obligation ≡ true

open PrecisionGravityInterpretationWitness public

record PrecisionThrustBoundary : Set where
  constructor precision-thrust-boundary
  field
    residualMagnitudeDoesNotCloseNuisance : Bool
    nuisanceClosureDoesNotByItselfIdentifyMechanism : Bool
    repeatedForceDoesNotByItselfIdentifyGravity : Bool
    gravityInterpretationNeedsIndependentConsumer : Bool
    declaredNuisanceListDoesNotClaimEachChannelIsClosed : Bool
    replicationMustBindSameClaimAndCalibration : Bool

open PrecisionThrustBoundary public

canonicalPrecisionThrustBoundary : PrecisionThrustBoundary
canonicalPrecisionThrustBoundary =
  precision-thrust-boundary true true true true true true
