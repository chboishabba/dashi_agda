module DASHI.Moonshine.OggSSPClimbingGymEmpiricalReplayExact where

------------------------------------------------------------------------
-- EXECUTABLE EMPIRICAL REPLAY RECEIPTS
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.RadixValuationStageBridge as Radix
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as SignedBranch
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.OggSSPClimbingGymFigureObservationExact as Figure
import DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact as Gym
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

-- scripts/monster_climbing_gym_replay.py independently reconstructs the ten
-- integer figure rows from the first 849 positive nontrivial zeta-zero
-- ordinates, h_m = 2*pi*m/(p^a*log p), the guard interval
-- [t_1 + 1, t_849 - 1], and deterministic mutual-nearest matching.
-- The same producer now also evaluates a deterministic midpoint grid over one
-- complete lattice-shift period.  That grid is consistent with every rounded
-- source mean/SD within the declared numerical tolerance, but the rounded
-- summaries do not identify the source's finite random sample or RNG seed.
-- The cache is mpmath-generated diagnostic data, not a formal zero certificate.

replayZeroCount : Nat
replayZeroCount = 849

replayGuardWholeUnits : Nat
replayGuardWholeUnits = 1

phaseGridSteps : Nat
phaseGridSteps = 720

record ReplayedFigureRow : Set where
  constructor replayed-figure-row
  field
    replayedForm : Gym.WallForm
    replayedHoles : Nat
    replayedMutualPairs : Nat

open ReplayedFigureRow public

p2Replay : ReplayedFigureRow
p2Replay = replayed-figure-row Gym.p2Exponent1 271 270
p3Replay : ReplayedFigureRow
p3Replay = replayed-figure-row Gym.p3Exponent1 644 581
p5Replay : ReplayedFigureRow
p5Replay = replayed-figure-row Gym.p5Exponent1 1571 820
p7Replay : ReplayedFigureRow
p7Replay = replayed-figure-row Gym.p7Exponent1 2660 845
p11Replay : ReplayedFigureRow
p11Replay = replayed-figure-row Gym.p11Exponent1 5151 849
p2SquaredReplay : ReplayedFigureRow
p2SquaredReplay = replayed-figure-row Gym.p2Exponent2 542 513
p3SquaredReplay : ReplayedFigureRow
p3SquaredReplay = replayed-figure-row Gym.p3Exponent2 1931 841
p2CubedReplay : ReplayedFigureRow
p2CubedReplay = replayed-figure-row Gym.p2Exponent3 1083 773
p13Replay : ReplayedFigureRow
p13Replay = replayed-figure-row Gym.p13Exponent1 6511 849
p71Replay : ReplayedFigureRow
p71Replay = replayed-figure-row Gym.p71Exponent1 59099 849

p2ReplayHolesExact : replayedHoles p2Replay ≡ Figure.holes Figure.p2Exponent1Row
p2ReplayHolesExact = refl
p2ReplayMutualExact : replayedMutualPairs p2Replay ≡ Figure.mutualPairs Figure.p2Exponent1Row
p2ReplayMutualExact = refl
p3ReplayHolesExact : replayedHoles p3Replay ≡ Figure.holes Figure.p3Exponent1Row
p3ReplayHolesExact = refl
p3ReplayMutualExact : replayedMutualPairs p3Replay ≡ Figure.mutualPairs Figure.p3Exponent1Row
p3ReplayMutualExact = refl
p5ReplayHolesExact : replayedHoles p5Replay ≡ Figure.holes Figure.p5Exponent1Row
p5ReplayHolesExact = refl
p5ReplayMutualExact : replayedMutualPairs p5Replay ≡ Figure.mutualPairs Figure.p5Exponent1Row
p5ReplayMutualExact = refl
p7ReplayHolesExact : replayedHoles p7Replay ≡ Figure.holes Figure.p7Exponent1Row
p7ReplayHolesExact = refl
p7ReplayMutualExact : replayedMutualPairs p7Replay ≡ Figure.mutualPairs Figure.p7Exponent1Row
p7ReplayMutualExact = refl
p11ReplayHolesExact : replayedHoles p11Replay ≡ Figure.holes Figure.p11Exponent1Row
p11ReplayHolesExact = refl
p11ReplayMutualExact : replayedMutualPairs p11Replay ≡ Figure.mutualPairs Figure.p11Exponent1Row
p11ReplayMutualExact = refl
p2SquaredReplayHolesExact : replayedHoles p2SquaredReplay ≡ Figure.holes Figure.p2Exponent2Row
p2SquaredReplayHolesExact = refl
p2SquaredReplayMutualExact : replayedMutualPairs p2SquaredReplay ≡ Figure.mutualPairs Figure.p2Exponent2Row
p2SquaredReplayMutualExact = refl
p3SquaredReplayHolesExact : replayedHoles p3SquaredReplay ≡ Figure.holes Figure.p3Exponent2Row
p3SquaredReplayHolesExact = refl
p3SquaredReplayMutualExact : replayedMutualPairs p3SquaredReplay ≡ Figure.mutualPairs Figure.p3Exponent2Row
p3SquaredReplayMutualExact = refl
p2CubedReplayHolesExact : replayedHoles p2CubedReplay ≡ Figure.holes Figure.p2Exponent3Row
p2CubedReplayHolesExact = refl
p2CubedReplayMutualExact : replayedMutualPairs p2CubedReplay ≡ Figure.mutualPairs Figure.p2Exponent3Row
p2CubedReplayMutualExact = refl
p13ReplayHolesExact : replayedHoles p13Replay ≡ Figure.holes Figure.p13Exponent1Row
p13ReplayHolesExact = refl
p13ReplayMutualExact : replayedMutualPairs p13Replay ≡ Figure.mutualPairs Figure.p13Exponent1Row
p13ReplayMutualExact = refl
p71ReplayHolesExact : replayedHoles p71Replay ≡ Figure.holes Figure.p71Exponent1Row
p71ReplayHolesExact = refl
p71ReplayMutualExact : replayedMutualPairs p71Replay ≡ Figure.mutualPairs Figure.p71Exponent1Row
p71ReplayMutualExact = refl
p71ReplaySaturates : replayedMutualPairs p71Replay ≡ replayZeroCount
p71ReplaySaturates = refl

------------------------------------------------------------------------
-- Non-Ogg control replay.
------------------------------------------------------------------------

record ControlReplayRow : Set where
  constructor control-replay-row
  field
    controlPrime : Matrix.OddPrimeCandidateUnder72
    controlHoles : Nat
    controlMutualPairs : Nat

open ControlReplayRow public

p37ControlReplay : ControlReplayRow
p37ControlReplay = control-replay-row Matrix.prime37 26090 849
p43ControlReplay : ControlReplayRow
p43ControlReplay = control-replay-row Matrix.prime43 31582 849
p53ControlReplay : ControlReplayRow
p53ControlReplay = control-replay-row Matrix.prime53 41091 849
p61ControlReplay : ControlReplayRow
p61ControlReplay = control-replay-row Matrix.prime61 48967 849
p67ControlReplay : ControlReplayRow
p67ControlReplay = control-replay-row Matrix.prime67 55012 849

p37ControlIsNonOgg : Matrix.externalOggLabel (controlPrime p37ControlReplay) ≡ false
p37ControlIsNonOgg = Matrix.prime37ExternallyNegative
p43ControlIsNonOgg : Matrix.externalOggLabel (controlPrime p43ControlReplay) ≡ false
p43ControlIsNonOgg = Matrix.prime43ExternallyNegative
p53ControlIsNonOgg : Matrix.externalOggLabel (controlPrime p53ControlReplay) ≡ false
p53ControlIsNonOgg = Matrix.prime53ExternallyNegative
p61ControlIsNonOgg : Matrix.externalOggLabel (controlPrime p61ControlReplay) ≡ false
p61ControlIsNonOgg = Matrix.prime61ExternallyNegative
p67ControlIsNonOgg : Matrix.externalOggLabel (controlPrime p67ControlReplay) ≡ false
p67ControlIsNonOgg = Matrix.prime67ExternallyNegative

p37ControlSaturates : controlMutualPairs p37ControlReplay ≡ replayZeroCount
p37ControlSaturates = refl
p43ControlSaturates : controlMutualPairs p43ControlReplay ≡ replayZeroCount
p43ControlSaturates = refl
p53ControlSaturates : controlMutualPairs p53ControlReplay ≡ replayZeroCount
p53ControlSaturates = refl
p61ControlSaturates : controlMutualPairs p61ControlReplay ≡ replayZeroCount
p61ControlSaturates = refl
p67ControlSaturates : controlMutualPairs p67ControlReplay ≡ replayZeroCount
p67ControlSaturates = refl

------------------------------------------------------------------------
-- Unsigned-observation obstruction.
------------------------------------------------------------------------

negativeP2Root : Gym.SignedRadixWallState 0
negativeP2Root =
  Gym.signed-radix-wall-state
    (SignedBranch.pointed-signed-ssp-lane
      Lane.p2 (Signed.negativeMultiplicity 1))
    Radix.radial-root

positiveP2Root : Gym.SignedRadixWallState 0
positiveP2Root =
  Gym.signed-radix-wall-state
    (SignedBranch.pointed-signed-ssp-lane
      Lane.p2 (Signed.positiveMultiplicity 1))
    Radix.radial-root

primeOnlyObservation : Gym.SignedRadixWallState 0 → Lane.MonsterPrimeLane
primeOnlyObservation = Gym.wallPrime

oppositeRootsPrimeCollision :
  primeOnlyObservation negativeP2Root ≡ primeOnlyObservation positiveP2Root
oppositeRootsPrimeCollision = refl

negativeRootOrientationInverse :
  Gym.wallOrientation negativeP2Root ≡ Signed.inverseOrientation
negativeRootOrientationInverse = refl

positiveRootOrientationForward :
  Gym.wallOrientation positiveP2Root ≡ Signed.forwardOrientation
positiveRootOrientationForward = refl

inverseOrientationNotForward :
  Signed.inverseOrientation ≡ Signed.forwardOrientation → ⊥
inverseOrientationNotForward ()

record PrimeOnlyOrientationDecoder : Set where
  field
    decodeOrientation : Lane.MonsterPrimeLane → Signed.FibreOrientation
    recoversOrientation :
      (state : Gym.SignedRadixWallState 0) →
      decodeOrientation (primeOnlyObservation state)
      ≡ Gym.wallOrientation state

open PrimeOnlyOrientationDecoder public

noPrimeOnlyOrientationDecoder : PrimeOnlyOrientationDecoder → ⊥
noPrimeOnlyOrientationDecoder decoder =
  inverseOrientationNotForward
    (trans
      (sym negativeRootOrientationInverse)
      (trans
        (sym (recoversOrientation decoder negativeP2Root))
        (trans
          (cong (decodeOrientation decoder) oppositeRootsPrimeCollision)
          (trans
            (recoversOrientation decoder positiveP2Root)
            positiveRootOrientationForward))))

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record ClimbingGymReplayBoundary : Set where
  constructor climbing-gym-replay-boundary
  field
    first849ZeroCacheCheckedIn : Bool
    oneUnitGuardReproducesAllTenHoleCounts : Bool
    mutualNearestReplayReproducesAllTenPairCounts : Bool
    p71ReplaySaturates849 : Bool
    nonOggControlSaturationShowsSaturationNotOggSpecific : Bool
    unsignedStatisticCannotRecoverSignedOrientation : Bool
    shiftedLatticeControlImplemented : Bool
    deterministicUniformPhaseGridNullImplemented : Bool
    sourceRoundedShiftSummariesCompatibleWithUniformPhaseNull : Bool
    reportedShiftControlSeedRecovered : Bool
    roundedSummariesIdentifyUniqueFiniteShiftSample : Bool
    numericalZeroCacheIsFormalZeroCertificate : Bool
    replayProvesRiemannHypothesis : Bool

open ClimbingGymReplayBoundary public

canonicalClimbingGymReplayBoundary : ClimbingGymReplayBoundary
canonicalClimbingGymReplayBoundary =
  climbing-gym-replay-boundary
    true true true true true true true true true false false false false
