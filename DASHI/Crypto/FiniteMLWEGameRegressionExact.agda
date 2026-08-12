module DASHI.Crypto.FiniteMLWEGameRegressionExact where

------------------------------------------------------------------------
-- FINITE MLWE LAB -> SECURITY-GAME COMPOSITION
--
-- The public value (2,2) contains two plausible hidden key states with opposite
-- protected first-secret-bit labels.  Therefore public observation alone cannot
-- deterministically recover that label and cannot support a perfect binary
-- distinguisher.  A hidden-dependent first-bit observation then shrinks the
-- finite candidate fibre from two to one in the lab.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Crypto.FiniteMLWEVectorLabExact as Lab
import DASHI.Crypto.FiniteSecurityGameBoundaryExact as Game
import DASHI.Crypto.FiniteCandidateFibreCardinalityExact as Count

labProtectedBit : Lab.HiddenState → Bool
labProtectedBit hidden = Lab.s0 (Lab.secret hidden)

labBinaryGame : Game.BinaryProtectedGame
labBinaryGame =
  Game.binaryProtectedGame
    Lab.HiddenState Lab.Public2
    Lab.hidden01 Lab.hidden10
    Lab.projectHidden labProtectedBit
    refl refl

labChallengeCollision : Game.ChallengeObservationCollision labBinaryGame
labChallengeCollision = Game.challengeObservationCollision refl

publicObservationCannotPerfectlyDistinguishLabSecrets :
  ∀ adversary →
  Game.PerfectDistinguisher labBinaryGame adversary → ⊥
publicObservationCannotPerfectlyDistinguishLabSecrets adversary =
  Game.collisionRefutesPerfectDistinguisher labChallengeCollision

publicObservationCannotExactlyRecoverProtectedBit :
  Game.ExactProtectedRecovery labBinaryGame → ⊥
publicObservationCannotExactlyRecoverProtectedBit =
  Game.collisionRefutesExactRecovery labChallengeCollision

labResidualTestLeavesTwo :
  Count.liveCount Lab.public22CandidateMask ≡ 2
labResidualTestLeavesTwo = refl

labHiddenObservationLeavesOne :
  Count.liveCount Lab.afterFirstBitFalseMask ≡ 1
labHiddenObservationLeavesOne = refl
