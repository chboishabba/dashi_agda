module DASHI.Moonshine.OggSSP2B279FirewalledCrossPollinationExact where

------------------------------------------------------------------------
-- 279 x MONSTER-2B CROSS-POLLINATION, WITH SAME-OBJECT FIREWALL
--
-- The merged 279 hub proves the exact scalar seam
--
--   279 = 9 * 31 = 3^2 * 31 = (101100)_3,
--
-- and ties 31 to the existing Monster/Ogg p31 lane.  The post-Brauer 2B
-- programme independently reaches a literal characteristic-two same-object
-- problem.  This module lets both facts coexist while proving by construction
-- that the arithmetic hub contributes no Q10 or outer-action witness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Moonshine.MonsterOgg279ProvenanceHubExact as N279
import DASHI.Moonshine.OggSSP2BPostBrauerSameObjectFrontierExact as TwoB

scalar279FromP31IsPaid :
  N279.nonaryScale * N279.monsterLane31Value ≡ N279.single279
scalar279FromP31IsPaid = N279.nonaryTimesMonster31Is279

ternary279IsPaid :
  243 + 27 + 9 ≡ N279.single279
ternary279IsPaid = N279.ternarySparseExpansionIs279

p31To279SameObjectPromotionRemainsEmpty :
  TwoB.P31To279SameObjectPromotionPaid → ⊥
p31To279SameObjectPromotionRemainsEmpty = TwoB.p31To279StillFirewalled

record TwoB279Boundary : Set where
  constructor two-b-279-boundary
  field
    scalar279ArithmeticPaid : Bool
    p31MonsterOggObserverPaid : Bool
    postBrauerSemisimplifiedIngressPaid : Bool
    arithmetic279PaysActualQ10 : Bool
    arithmetic279PaysOuterActionDescent : Bool
    arithmetic279PaysDefectOrientationBits : Bool

open TwoB279Boundary public

canonical279TwoBBoundary : TwoB279Boundary
canonical279TwoBBoundary =
  two-b-279-boundary
    true true true
    false false false
