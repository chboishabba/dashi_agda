module DASHI.Physics.Closure.NSTriadKNIntrospectiveCriticalLeafObserverRound509Exact where

------------------------------------------------------------------------
-- ROUND509 / INTROSPECTIVE AUDIT OF THE SECOND R504 TERMINAL LEAF
--
-- Apply the repository's introspective proof-loop discipline literally:
--
--   two proof states
--   -> current observer maps them to the same observation
--   -> downstream consumer requires different answers
--   -> name the first missing coordinate
--   -> refine the observer before doing more proof search.
--
-- R508 observes only
--
--   (physical signed-critical payment, literal-R406 remainder weld).
--
-- But R421's actual consumer additionally requires one cutoff-uniform initial
-- critical ceiling.  Therefore the two states
--
--   x = payment=true, weld=true, ceiling=false
--   y = payment=true, weld=true, ceiling=true
--
-- are observationally identical to the R508 two-bit observer while the R421
-- consumer must answer differently.  The missing coordinate is exactly the
-- initial-critical ceiling receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504
import DASHI.Physics.Closure.NSTriadKNLiteralR406CriticalProductionProofSearchRound508Exact as R508
import DASHI.Physics.Closure.NSTriadKNSignedHeatCrossDirectToCriticalBarrierRound421Exact as R421

record RefinedCriticalLeafStatus : Set where
  constructor refined-critical-leaf-status
  field
    physicalSignedCriticalPaymentPresent : Bool
    literalR406RemainderWeldPresent : Bool
    uniformInitialCriticalCeilingPresent : Bool

open RefinedCriticalLeafStatus public

-- The old R508 observation forgets the ceiling coordinate.
oldR508Observer : RefinedCriticalLeafStatus → Bool × Bool
oldR508Observer S =
  physicalSignedCriticalPaymentPresent S , literalR406RemainderWeldPresent S

xMissingCeiling : RefinedCriticalLeafStatus
xMissingCeiling = refined-critical-leaf-status true true false

yFullyReady : RefinedCriticalLeafStatus
yFullyReady = refined-critical-leaf-status true true true

oldObserverCollision :
  oldR508Observer xMissingCeiling ≡ oldR508Observer yFullyReady
oldObserverCollision = refl

data RefinedCriticalResidual : Set where
  missingPhysicalSignedCriticalPayment : RefinedCriticalResidual
  missingLiteralR406RemainderWeld : RefinedCriticalResidual
  missingUniformInitialCriticalCeiling : RefinedCriticalResidual
  refinedCriticalLeafClosed : RefinedCriticalResidual

firstRefinedResidual : RefinedCriticalLeafStatus → RefinedCriticalResidual
firstRefinedResidual (refined-critical-leaf-status false weld ceiling) =
  missingPhysicalSignedCriticalPayment
firstRefinedResidual (refined-critical-leaf-status true false ceiling) =
  missingLiteralR406RemainderWeld
firstRefinedResidual (refined-critical-leaf-status true true false) =
  missingUniformInitialCriticalCeiling
firstRefinedResidual (refined-critical-leaf-status true true true) =
  refinedCriticalLeafClosed

consumerDistinguishesCollisionLeft :
  firstRefinedResidual xMissingCeiling ≡ missingUniformInitialCriticalCeiling
consumerDistinguishesCollisionLeft = refl

consumerDistinguishesCollisionRight :
  firstRefinedResidual yFullyReady ≡ refinedCriticalLeafClosed
consumerDistinguishesCollisionRight = refl

currentRefinedStatus : RefinedCriticalLeafStatus
currentRefinedStatus = refined-critical-leaf-status false false false

currentFirstRefinedResidual :
  firstRefinedResidual currentRefinedStatus
  ≡ missingPhysicalSignedCriticalPayment
currentFirstRefinedResidual = refl

------------------------------------------------------------------------
-- Cross-check against the actual downstream/current surfaces.
------------------------------------------------------------------------

round509R504SecondLeafStillOpen : Bool
round509R504SecondLeafStillOpen =
  R504.round504CriticalProductionSliceClosed

round509R508PhysicalPaymentStillOpen : Bool
round509R508PhysicalPaymentStillOpen =
  R508.round508Round104PhysicalSignedCriticalProductionClosed

round509R508RemainderWeldStillOpen : Bool
round509R508RemainderWeldStillOpen =
  R508.round508R507RemainderWeldClosed

-- R421 explicitly carries a separate uniformInitialCeiling and theorem
-- uniformInitialCritical; this is why the third coordinate is consumer-visible.
round509R421RequiresSeparateInitialCeilingCoordinate : Bool
round509R421RequiresSeparateInitialCeilingCoordinate = true

round509OldR508ObserverAdequateForR421Consumer : Bool
round509OldR508ObserverAdequateForR421Consumer = false

round509RefinedObserverAddsOnlyMissingCoordinate : Bool
round509RefinedObserverAddsOnlyMissingCoordinate = true

round509ClayPromotion : Bool
round509ClayPromotion = false

round509R421RequiresSeparateInitialCeilingCoordinateIsTrue :
  round509R421RequiresSeparateInitialCeilingCoordinate ≡ true
round509R421RequiresSeparateInitialCeilingCoordinateIsTrue = refl

round509OldR508ObserverAdequateForR421ConsumerIsFalse :
  round509OldR508ObserverAdequateForR421Consumer ≡ false
round509OldR508ObserverAdequateForR421ConsumerIsFalse = refl

round509RefinedObserverAddsOnlyMissingCoordinateIsTrue :
  round509RefinedObserverAddsOnlyMissingCoordinate ≡ true
round509RefinedObserverAddsOnlyMissingCoordinateIsTrue = refl

round509ClayPromotionIsFalse : round509ClayPromotion ≡ false
round509ClayPromotionIsFalse = refl
