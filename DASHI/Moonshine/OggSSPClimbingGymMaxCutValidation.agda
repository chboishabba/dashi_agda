module DASHI.Moonshine.OggSSPClimbingGymMaxCutValidation where

open import DASHI.Core.Prelude

import DASHI.Analysis.RiemannSSP15FilteredProvenanceCapstoneExact as Capstone
import DASHI.Analysis.RiemannSSP15ProducerMarkedClimbingGymBridgeExact as RHGym
import DASHI.Analysis.RiemannSSP15DepthFiveRoleCodecExact as RHCodec
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Quotient
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.RadixValuationStageBridge as Radix
import DASHI.Foundations.StratifiedResolutionTowerExact as Tower
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as SignedBranch
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact as Gym
import DASHI.Moonshine.OggSSPClimbingGymFigureObservationExact as Figure
import DASHI.Moonshine.OggSSPSignedRadixInverseLimitExact as Limit
import DASHI.Moonshine.OggSSPClimbingGymEmpiricalReplayExact as Replay
import DASHI.Moonshine.OggSSPClimbingGymAnalyticRadixAdapterExact as Analytic

------------------------------------------------------------------------
-- TDD regression contract.
------------------------------------------------------------------------

p2RadixIsTwo :
  Radix.radix (Gym.oggPrimeRadixChart Lane.p2) ≡ 2
p2RadixIsTwo = refl

p71RadixIsSeventyOne :
  Radix.radix (Gym.oggPrimeRadixChart Lane.p71) ≡ 71
p71RadixIsSeventyOne = refl

signedCarrierBridgeReusedAtP47 :
  SignedBranch.lanePrimeToSignedPrime Lane.p47 ≡ Signed.ssp47
signedCarrierBridgeReusedAtP47 = refl

coarseningCommutesWithSignedNegation :
  ∀ {depth}
    (state : Gym.SignedRadixWallState (suc depth)) →
  Gym.coarsenSignedRadixWall (Gym.negateSignedRadixWall state)
  ≡
  Gym.negateSignedRadixWall (Gym.coarsenSignedRadixWall state)
coarseningCommutesWithSignedNegation =
  Gym.coarsenNegationCommutes

p2FirstFormNIsTwo :
  Gym.wallFormN Gym.p2Exponent1 ≡ 2
p2FirstFormNIsTwo = refl

p2SquaredFormNIsFour :
  Gym.wallFormN Gym.p2Exponent2 ≡ 4
p2SquaredFormNIsFour = refl

p3SquaredFormNIsNine :
  Gym.wallFormN Gym.p3Exponent2 ≡ 9
p3SquaredFormNIsNine = refl

p2CubedFormNIsEight :
  Gym.wallFormN Gym.p2Exponent3 ≡ 8
p2CubedFormNIsEight = refl

figureZeroCountIs849 :
  Figure.figureZeroCount ≡ 849
figureZeroCountIs849 = refl

p11FigureSaturates :
  Figure.mutualPairs Figure.p11Exponent1Row ≡ Figure.figureZeroCount
p11FigureSaturates = refl

p13FigureSaturates :
  Figure.mutualPairs Figure.p13Exponent1Row ≡ Figure.figureZeroCount
p13FigureSaturates = refl

p71FigureSaturates :
  Figure.mutualPairs Figure.p71Exponent1Row ≡ Figure.figureZeroCount
p71FigureSaturates = refl

saturatedCountCannotRecoverOggLane :
  Figure.MutualCountLaneDecoder → ⊥
saturatedCountCannotRecoverOggLane =
  Figure.noMutualCountLaneDecoder

figurePrimeLaneIsTypedCanonical :
  (row : Figure.ClimbingGymFigureRow) →
  Lane.MonsterPrimeLane
figurePrimeLaneIsTypedCanonical = Figure.figureLane

signedRadixTowerCarrierAt :
  (depth : Nat) →
  Tower.Carrier Limit.signedRadixWallTower depth
  ≡ Gym.SignedRadixWallState depth
signedRadixTowerCarrierAt depth = refl

negatedHistoryRemainsCoherent :
  (history : Limit.SignedRadixHistory)
  (depth : Nat) →
  Tower.project Limit.signedRadixWallTower
    (Tower.atResolution (Limit.negateHistory history) (suc depth))
  ≡
  Tower.atResolution (Limit.negateHistory history) depth
negatedHistoryRemainsCoherent history depth =
  Tower.coherent (Limit.negateHistory history) depth

producerMarkedOriginRootIsInverse :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) →
  Gym.wallOrientation
    (RHGym.producerMarkedRootWall
      (Capstone.canonicalProducerMarkedCode
        certificate Quotient.mode18 RHCodec.originRole))
  ≡ Signed.inverseOrientation
producerMarkedOriginRootIsInverse =
  RHGym.originRoleRootWallOrientationInverse

producerMarkedJRootRetainsP11 :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) →
  Gym.wallPrime
    (RHGym.producerMarkedRootWall
      (Capstone.canonicalProducerMarkedCode
        certificate Quotient.mode18 RHCodec.jRole))
  ≡ Lane.p11
producerMarkedJRootRetainsP11 =
  RHGym.jMode18RootWallPrimeIsEleven

producerMarkedSRootIsForward :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) →
  Gym.wallOrientation
    (RHGym.producerMarkedRootWall
      (Capstone.canonicalProducerMarkedCode
        certificate Quotient.mode18 RHCodec.sRole))
  ≡ Signed.forwardOrientation
producerMarkedSRootIsForward =
  RHGym.sRoleRootWallOrientationForward

------------------------------------------------------------------------
-- Empirical replay regression: the executable producer independently
-- reproduces every supplied hole/mutual row from 849 zeros and guard = 1.
------------------------------------------------------------------------

replayUses849Zeros : Replay.replayZeroCount ≡ 849
replayUses849Zeros = refl

replayUsesOneUnitGuard : Replay.replayGuardWholeUnits ≡ 1
replayUsesOneUnitGuard = refl

replayP2MatchesFigure :
  Replay.replayedHoles Replay.p2Replay ≡ Figure.holes Figure.p2Exponent1Row
replayP2MatchesFigure = refl

replayP3MatchesFigure :
  Replay.replayedMutualPairs Replay.p3Replay
  ≡ Figure.mutualPairs Figure.p3Exponent1Row
replayP3MatchesFigure = refl

replayP71Saturates :
  Replay.replayedMutualPairs Replay.p71Replay ≡ Replay.replayZeroCount
replayP71Saturates = refl

unsignedReplayCannotRecoverSignedOrientation :
  Replay.PrimeOnlyOrientationDecoder → ⊥
unsignedReplayCannotRecoverSignedOrientation =
  Replay.noPrimeOnlyOrientationDecoder

reportedShiftControlsRemainSeedUnrecovered :
  Replay.reportedShiftControlSeedRecovered
    Replay.canonicalClimbingGymReplayBoundary
  ≡ false
reportedShiftControlsRemainSeedUnrecovered = refl

------------------------------------------------------------------------
-- Analytic adapter regression: constructive log/pi are reused, while the
-- missing real-to-finite quantisation authority remains explicit.
------------------------------------------------------------------------

analyticAdapterReusesConstructiveLog :
  Analytic.analyticLogarithmReused
    Analytic.canonicalAnalyticRadixAdapterBoundary
  ≡ true
analyticAdapterReusesConstructiveLog = refl

analyticAdapterDoesNotFabricateFloor :
  Analytic.floorQuantisationConstructedFromCurrentRealSpine
    Analytic.canonicalAnalyticRadixAdapterBoundary
  ≡ false
analyticAdapterDoesNotFabricateFloor = refl

boundaryKeepsAddressAndSignedFlowDistinct :
  Gym.signedValuationIsRadixAddress
    Gym.canonicalOggSSPSignedRadixClimbingGymBoundary
  ≡ false
boundaryKeepsAddressAndSignedFlowDistinct = refl

boundaryKeepsObservationOutOfRHPromotion :
  Figure.figureObservationProvesZetaZeroParametrisation
    Figure.canonicalClimbingGymFigureObservationBoundary
  ≡ false
boundaryKeepsObservationOutOfRHPromotion = refl

boundaryKeepsInverseLimitFiniteStructural :
  Limit.inverseLimitConstructsAnalyticPAdicCompletion
    Limit.canonicalSignedRadixInverseLimitBoundary
  ≡ false
boundaryKeepsInverseLimitFiniteStructural = refl

boundaryKeepsRHProducerSeparateFromHoleObservation :
  RHGym.producerMarkedRootWallIdentifiesJMDHoleObservation
    RHGym.canonicalRiemannSSP15ProducerMarkedClimbingGymBoundary
  ≡ false
boundaryKeepsRHProducerSeparateFromHoleObservation = refl
