module DASHI.Economics.AIOpenWeightTrajectory20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIOpenWeightMarketTransition2026Exact as Prior
import DASHI.Economics.AIMarketOpenWeightFreshAcquisition20261012Exact as Fresh

------------------------------------------------------------------------
-- SAME-PLATFORM OPEN-WEIGHT TOKEN-SHARE TRAJECTORY
--
-- August 2026: 56% Vercel AI Gateway token volume (existing source owner).
-- October 10 2026: 61.3% on the current Vercel leaderboard.
------------------------------------------------------------------------

record PlatformOpenWeightTrajectory : Set where
  constructor platformOpenWeightTrajectory
  field
    platform : String
    metric : String
    earlierShareBp : Nat
    laterShareBp : Nat
    absoluteChangeBp : Nat
    laterGreater : Bool
    platformLocalPersistenceObserved : Bool
    globalMarketTrajectoryClosed : Bool
    equalCapabilitySubstitutionClosed : Bool

open PlatformOpenWeightTrajectory public

vercelOpenWeightTrajectory : PlatformOpenWeightTrajectory
vercelOpenWeightTrajectory = platformOpenWeightTrajectory
  "Vercel AI Gateway"
  "open-weight share of token volume"
  5600 6130 530 true true false false

------------------------------------------------------------------------
-- Scope firewalls.
------------------------------------------------------------------------

data PlatformTrajectoryImpliesGlobalTrajectoryPermission : Set where
data UsageShareIncreaseImpliesEqualCapabilityPermission : Set where
data UsageShareIncreaseImpliesRentCollapsePermission : Set where

platformTrajectoryDoesNotAutoBecomeGlobal : PlatformTrajectoryImpliesGlobalTrajectoryPermission → ⊥
platformTrajectoryDoesNotAutoBecomeGlobal ()

usageShareIncreaseDoesNotAutoProveEqualCapability : UsageShareIncreaseImpliesEqualCapabilityPermission → ⊥
usageShareIncreaseDoesNotAutoProveEqualCapability ()

usageShareIncreaseDoesNotAutoProveRentCollapse : UsageShareIncreaseImpliesRentCollapsePermission → ⊥
usageShareIncreaseDoesNotAutoProveRentCollapse ()

vercelTrajectoryRisesBy530bp : absoluteChangeBp vercelOpenWeightTrajectory ≡ 530
vercelTrajectoryRisesBy530bp = refl

platformPersistenceIsObserved : platformLocalPersistenceObserved vercelOpenWeightTrajectory ≡ true
platformPersistenceIsObserved = refl

globalTrajectoryStillOpen : globalMarketTrajectoryClosed vercelOpenWeightTrajectory ≡ false
globalTrajectoryStillOpen = refl
