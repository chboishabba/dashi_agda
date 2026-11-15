module DASHI.Moonshine.OggSSPClimbingGymConsumerDescentExact where

------------------------------------------------------------------------
-- CANONICAL CONSUMER-DESCENT WELD
--
-- The climbing-gym branch already had two concrete decoder obstructions:
--
-- * saturated mutual-pair count cannot recover Ogg lane identity;
-- * prime-only observation cannot recover signed FRACTRAN orientation.
--
-- This owner projects those literal collisions into the repository's canonical
-- ConsumerNonDescentWitness / ConsumerSufficient / FactorsThrough spine.
-- Nothing new is assumed about the empirical data.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Moonshine.OggSSPClimbingGymFigureObservationExact as Figure
import DASHI.Moonshine.OggSSPClimbingGymEmpiricalReplayExact as Replay
import DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact as Gym
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- 1. Saturated count is insufficient for the lane-identity consumer.
------------------------------------------------------------------------

mutualCountLaneNonDescent :
  Descent.ConsumerNonDescentWitness Figure.mutualPairs Figure.figureLane
mutualCountLaneNonDescent =
  Descent.consumerNonDescentWitness
    Figure.p11Exponent1Row
    Figure.p13Exponent1Row
    Figure.p11P13MutualCountCollision
    Figure.p11P13LanesDistinct

mutualCountNotLaneSufficient :
  Descent.ConsumerSufficient Figure.mutualPairs Figure.figureLane → ⊥
mutualCountNotLaneSufficient =
  Descent.nonDescentWitnessBlocksSufficiency mutualCountLaneNonDescent

mutualCountCannotFactorLane :
  Descent.FactorsThrough Figure.mutualPairs Figure.figureLane → ⊥
mutualCountCannotFactorLane =
  Descent.nonDescentWitnessBlocksFactorization mutualCountLaneNonDescent

laneIdentityObserverIsLeastSufficient :
  Descent.LeastSufficientConsumerObserver Figure.figureLane
laneIdentityObserverIsLeastSufficient =
  Descent.canonicalConsumerObserverIsLeast Figure.figureLane

------------------------------------------------------------------------
-- 2. Prime-only observation is insufficient for signed orientation.
------------------------------------------------------------------------

orientationConsumer :
  Gym.SignedRadixWallState 0 → Signed.FibreOrientation
orientationConsumer = Gym.wallOrientation

primeOnlyOrientationNonDescent :
  Descent.ConsumerNonDescentWitness
    Replay.primeOnlyObservation
    orientationConsumer
primeOnlyOrientationNonDescent =
  Descent.consumerNonDescentWitness
    Replay.negativeP2Root
    Replay.positiveP2Root
    Replay.oppositeRootsPrimeCollision
    Replay.inverseOrientationNotForward

primeOnlyNotOrientationSufficient :
  Descent.ConsumerSufficient
    Replay.primeOnlyObservation
    orientationConsumer → ⊥
primeOnlyNotOrientationSufficient =
  Descent.nonDescentWitnessBlocksSufficiency primeOnlyOrientationNonDescent

primeOnlyCannotFactorOrientation :
  Descent.FactorsThrough
    Replay.primeOnlyObservation
    orientationConsumer → ⊥
primeOnlyCannotFactorOrientation =
  Descent.nonDescentWitnessBlocksFactorization primeOnlyOrientationNonDescent

orientationObserverIsLeastSufficient :
  Descent.LeastSufficientConsumerObserver orientationConsumer
orientationObserverIsLeastSufficient =
  Descent.canonicalConsumerObserverIsLeast orientationConsumer

------------------------------------------------------------------------
-- 3. Boundary.
------------------------------------------------------------------------

record ClimbingGymConsumerDescentBoundary : Set where
  constructor climbing-gym-consumer-descent-boundary
  field
    saturationCollisionUsesCanonicalNonDescent : Bool
    saturationBlocksLaneSufficiency : Bool
    saturationBlocksLaneFactorisation : Bool
    signedCollisionUsesCanonicalNonDescent : Bool
    primeOnlyBlocksOrientationSufficiency : Bool
    primeOnlyBlocksOrientationFactorisation : Bool
    consumerObserverMinimalityReused : Bool

    nonDescentMeansSourceDataFalse : Bool
    nonDescentCreatesMonsterSpecificity : Bool
    oneObserverDeclaredSufficientForEveryConsumer : Bool

open ClimbingGymConsumerDescentBoundary public

canonicalClimbingGymConsumerDescentBoundary : ClimbingGymConsumerDescentBoundary
canonicalClimbingGymConsumerDescentBoundary =
  climbing-gym-consumer-descent-boundary
    true true true true true true true
    false false false
