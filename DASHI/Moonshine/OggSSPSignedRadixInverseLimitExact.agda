module DASHI.Moonshine.OggSSPSignedRadixInverseLimitExact where

------------------------------------------------------------------------
-- SIGNED OGG / SSP RADIX WALL AS A RESOLUTION TOWER
--
-- Reuse the repository's generic resolution-tower / inverse-limit machinery
-- to express an infinite compatible climbing path.  This is stronger and more
-- precise than calling one finite address "p-adic", while remaining weaker
-- than constructing an analytic p-adic field/completion.
--
-- Signed negation acts levelwise and is coherent because the finite wall
-- theorem already proves that sign negation commutes with radix coarsening.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

import DASHI.Foundations.StratifiedResolutionTowerExact as Tower
import DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact as Gym

------------------------------------------------------------------------
-- 1. The whole dependent signed wall family is one resolution tower.
------------------------------------------------------------------------

signedRadixWallTower : Tower.ResolutionTower
signedRadixWallTower = record
  { Carrier = Gym.SignedRadixWallState
  ; project = Gym.coarsenSignedRadixWall
  }

SignedRadixHistory : Set₁
SignedRadixHistory = Tower.InverseLimitPoint signedRadixWallTower

historyAt : SignedRadixHistory → (depth : Nat) → Gym.SignedRadixWallState depth
historyAt history depth = Tower.atResolution history depth

historyCoherent :
  (history : SignedRadixHistory) →
  (depth : Nat) →
  Gym.coarsenSignedRadixWall (historyAt history (suc depth))
  ≡ historyAt history depth
historyCoherent history depth = Tower.coherent history depth

------------------------------------------------------------------------
-- 2. Signed negation transports coherent histories to coherent histories.
------------------------------------------------------------------------

negateHistory : SignedRadixHistory → SignedRadixHistory
negateHistory history =
  Tower.inverseLimitPoint
    (λ depth → Gym.negateSignedRadixWall (historyAt history depth))
    coherence
  where
    coherence :
      (depth : Nat) →
      Gym.coarsenSignedRadixWall
        (Gym.negateSignedRadixWall (historyAt history (suc depth)))
      ≡
      Gym.negateSignedRadixWall (historyAt history depth)
    coherence depth =
      trans
        (Gym.coarsenNegationCommutes (historyAt history (suc depth)))
        (cong Gym.negateSignedRadixWall (historyCoherent history depth))

negateHistoryTwiceAt :
  (history : SignedRadixHistory) →
  (depth : Nat) →
  historyAt (negateHistory (negateHistory history)) depth
  ≡ historyAt history depth
negateHistoryTwiceAt history depth =
  Gym.negateTwice (historyAt history depth)

negateHistoryPreservesPrimeAt :
  (history : SignedRadixHistory) →
  (depth : Nat) →
  Gym.wallPrime (historyAt (negateHistory history) depth)
  ≡ Gym.wallPrime (historyAt history depth)
negateHistoryPreservesPrimeAt history depth =
  Gym.negatePreservesPrime (historyAt history depth)

------------------------------------------------------------------------
-- 3. Coarse shadows are the existing generic tower shadows.
------------------------------------------------------------------------

historyCoarseShadow :
  SignedRadixHistory →
  (depth : Nat) →
  Gym.SignedRadixWallState depth
historyCoarseShadow history depth =
  Tower.coarseShadow history depth

historyCoarseShadowCoherent :
  (history : SignedRadixHistory) →
  (depth : Nat) →
  Gym.coarsenSignedRadixWall (historyCoarseShadow history (suc depth))
  ≡ historyCoarseShadow history depth
historyCoarseShadowCoherent history depth =
  Tower.coarseShadowCoherence history depth

------------------------------------------------------------------------
-- 4. Authority boundary.
------------------------------------------------------------------------

record SignedRadixInverseLimitBoundary : Set where
  constructor signed-radix-inverse-limit-boundary
  field
    resolutionTowerReused : Bool
    compatibleInfiniteHistoryTyped : Bool
    levelwiseSignedNegationPreservesCoherence : Bool
    levelwiseNegationInvolutive : Bool
    primeLanePreservedUnderSignedNegation : Bool

    inverseLimitConstructsAnalyticPAdicCompletion : Bool
    inverseLimitConstructsPAdicNorm : Bool
    compatibleHistoryIsAutomaticallyZetaZero : Bool
    compatibleHistoryProvesRiemannHypothesis : Bool

open SignedRadixInverseLimitBoundary public

canonicalSignedRadixInverseLimitBoundary :
  SignedRadixInverseLimitBoundary
canonicalSignedRadixInverseLimitBoundary =
  signed-radix-inverse-limit-boundary
    true true true true true
    false false false false
