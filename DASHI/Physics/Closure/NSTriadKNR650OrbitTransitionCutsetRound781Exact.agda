{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650OrbitTransitionCutsetRound781Exact where

------------------------------------------------------------------------
-- ROUND781 / ORBIT-TRANSITION CUTSET AFTER HH/LH/HL GEOMETRY
--
-- R777-R778:
--   HH base -> both cyclic nested rows have LH outer incidence.
--
-- R779:
--   LH base -> pEnergyLeg has a width-one input pair (k,-q), with output p.
--
-- R780:
--   HL base -> qEnergyLeg has a width-one input pair (k,-p), with output q.
--
-- Thus the orbit-profile search is no longer unconstrained.  The remaining
-- exact question is the strict Csep=3 boundary classification of those
-- width-one-input cyclic rows (HH versus CC), together with the complementary
-- cyclic leg for LH/HL and the native CC channel.
--
-- This file is a cutset/ownership module only.  It introduces no estimate,
-- sign, or promoted W2 claim.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNR650HHOrbitProfileRound777Exact as R777
import DASHI.Physics.Closure.NSTriadKNR650HHNestedRowsRouteToLHRound778Exact as R778
import DASHI.Physics.Closure.NSTriadKNR650LHOrbitDominantPairRound779Exact as R779
import DASHI.Physics.Closure.NSTriadKNR650HLOrbitDominantPairRound780Exact as R780

round781HHBothCyclicRowsRouteToLH : Bool
round781HHBothCyclicRowsRouteToLH =
  R778.round778HHBaseCyclicPRowIsLH

round781LHPRowInputPairWidthOne : Bool
round781LHPRowInputPairWidthOne =
  R779.round779LHPEnergyInputPairWidthOne

round781HLQRowInputPairWidthOne : Bool
round781HLQRowInputPairWidthOne =
  R780.round780HLQEnergyInputPairWidthOne

round781WidthOneRowsHaveForcedFullR25Class : Bool
round781WidthOneRowsHaveForcedFullR25Class = false

round781ComparableChannelResolved : Bool
round781ComparableChannelResolved = false

round781IntroducesEstimate : Bool
round781IntroducesEstimate = false

round781W2Closed : Bool
round781W2Closed = false

round781ClayPromotion : Bool
round781ClayPromotion = false

round781HHBothCyclicRowsRouteToLHIsTrue :
  round781HHBothCyclicRowsRouteToLH ≡ true
round781HHBothCyclicRowsRouteToLHIsTrue =
  R778.round778HHBaseCyclicPRowIsLHIsTrue

round781LHPRowInputPairWidthOneIsTrue :
  round781LHPRowInputPairWidthOne ≡ true
round781LHPRowInputPairWidthOneIsTrue =
  R779.round779LHPEnergyInputPairWidthOneIsTrue

round781HLQRowInputPairWidthOneIsTrue :
  round781HLQRowInputPairWidthOne ≡ true
round781HLQRowInputPairWidthOneIsTrue =
  R780.round780HLQEnergyInputPairWidthOneIsTrue

round781WidthOneRowsHaveForcedFullR25ClassIsFalse :
  round781WidthOneRowsHaveForcedFullR25Class ≡ false
round781WidthOneRowsHaveForcedFullR25ClassIsFalse = refl

round781ComparableChannelResolvedIsFalse :
  round781ComparableChannelResolved ≡ false
round781ComparableChannelResolvedIsFalse = refl

round781IntroducesEstimateIsFalse :
  round781IntroducesEstimate ≡ false
round781IntroducesEstimateIsFalse = refl

round781W2ClosedIsFalse :
  round781W2Closed ≡ false
round781W2ClosedIsFalse = refl

round781ClayPromotionIsFalse :
  round781ClayPromotion ≡ false
round781ClayPromotionIsFalse = refl
