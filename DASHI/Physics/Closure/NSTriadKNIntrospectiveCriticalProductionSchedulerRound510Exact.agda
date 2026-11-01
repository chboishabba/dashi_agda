module DASHI.Physics.Closure.NSTriadKNIntrospectiveCriticalProductionSchedulerRound510Exact where

------------------------------------------------------------------------
-- ROUND510 / INTROSPECTIVE REFINEMENT OF THE SECOND TERMINAL LEAF
--
-- R509 found an actual observer collision: R508 forgot the separate uniform
-- initial-critical ceiling consumed by R421.  This owner keeps the smallest
-- refined three-coordinate observer and schedules only the first missing
-- coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNIntrospectiveCriticalLeafObserverRound509Exact as R509
import DASHI.Physics.Closure.NSTriadKNLiteralR406CriticalProductionProofSearchRound508Exact as R508
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240

data CriticalLeafResidual : Set where
  missingPhysicalSignedCriticalPayment : CriticalLeafResidual
  missingLiteralR406RemainderWeld : CriticalLeafResidual
  missingUniformInitialCriticalCeiling : CriticalLeafResidual
  criticalLeafClosed : CriticalLeafResidual

record CriticalLeafStatus : Set where
  constructor critical-leaf-status
  field
    physicalSignedCriticalPaymentPresent : Bool
    literalR406RemainderWeldPresent : Bool
    uniformInitialCriticalCeilingPresent : Bool

open CriticalLeafStatus public

firstMissing : CriticalLeafStatus → CriticalLeafResidual
firstMissing (critical-leaf-status false weld ceiling) =
  missingPhysicalSignedCriticalPayment
firstMissing (critical-leaf-status true false ceiling) =
  missingLiteralR406RemainderWeld
firstMissing (critical-leaf-status true true false) =
  missingUniformInitialCriticalCeiling
firstMissing (critical-leaf-status true true true) = criticalLeafClosed

data ProducerClass : Set where
  signedNetworkCancellationProducer : ProducerClass
  sameObjectR406Producer : ProducerClass
  initialCriticalRealizationProducer : ProducerClass
  noProducerNeeded : ProducerClass

producerFor : CriticalLeafResidual → ProducerClass
producerFor missingPhysicalSignedCriticalPayment =
  signedNetworkCancellationProducer
producerFor missingLiteralR406RemainderWeld =
  sameObjectR406Producer
producerFor missingUniformInitialCriticalCeiling =
  initialCriticalRealizationProducer
producerFor criticalLeafClosed = noProducerNeeded

data Mechanism : Set where
  ThinkExternalCrossTriadSignedPayment : Mechanism
  LookSameObjectR406Remainder : Mechanism
  LookLiteralInitialCriticalRealization : Mechanism
  CompileCriticalLeaf : Mechanism

mechanismFor : CriticalLeafResidual → Mechanism
mechanismFor missingPhysicalSignedCriticalPayment =
  ThinkExternalCrossTriadSignedPayment
mechanismFor missingLiteralR406RemainderWeld =
  LookSameObjectR406Remainder
mechanismFor missingUniformInitialCriticalCeiling =
  LookLiteralInitialCriticalRealization
mechanismFor criticalLeafClosed = CompileCriticalLeaf

currentStatus : CriticalLeafStatus
currentStatus = critical-leaf-status false false false

currentFirstMissing :
  firstMissing currentStatus ≡ missingPhysicalSignedCriticalPayment
currentFirstMissing = refl

currentMechanism :
  mechanismFor (firstMissing currentStatus)
  ≡ ThinkExternalCrossTriadSignedPayment
currentMechanism = refl

-- Regression: after payment and remainder weld, the observer must not close.
afterPaymentAndWeld : CriticalLeafStatus
afterPaymentAndWeld = critical-leaf-status true true false

afterPaymentAndWeldStillNeedsInitialCeiling :
  firstMissing afterPaymentAndWeld ≡ missingUniformInitialCriticalCeiling
afterPaymentAndWeldStillNeedsInitialCeiling = refl

round510R509ObserverCollisionDetected : Bool
round510R509ObserverCollisionDetected = true

round510R508TwoCoordinateObserverSufficient : Bool
round510R508TwoCoordinateObserverSufficient = false

round510Round240CommonInitialDatumOwned : Bool
round510Round240CommonInitialDatumOwned =
  R240.round240CorrectedTrajectoryOwnsCommonInitialDatum

round510UniformInitialCriticalCeilingClosed : Bool
round510UniformInitialCriticalCeilingClosed = false

round510ClayPromotion : Bool
round510ClayPromotion = false

round510R509ObserverCollisionDetectedIsTrue :
  round510R509ObserverCollisionDetected ≡ true
round510R509ObserverCollisionDetectedIsTrue = refl

round510R508TwoCoordinateObserverSufficientIsFalse :
  round510R508TwoCoordinateObserverSufficient ≡ false
round510R508TwoCoordinateObserverSufficientIsFalse = refl

round510Round240CommonInitialDatumOwnedIsTrue :
  round510Round240CommonInitialDatumOwned ≡ true
round510Round240CommonInitialDatumOwnedIsTrue =
  R240.round240CorrectedTrajectoryOwnsCommonInitialDatumIsTrue

round510UniformInitialCriticalCeilingClosedIsFalse :
  round510UniformInitialCriticalCeilingClosed ≡ false
round510UniformInitialCriticalCeilingClosedIsFalse = refl

round510ClayPromotionIsFalse : round510ClayPromotion ≡ false
round510ClayPromotionIsFalse = refl
