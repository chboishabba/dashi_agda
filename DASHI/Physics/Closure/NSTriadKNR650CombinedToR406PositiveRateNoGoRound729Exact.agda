{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CombinedToR406PositiveRateNoGoRound729Exact where

------------------------------------------------------------------------
-- ROUND729 / R726 CANNOT BE DISCHARGED BY POSITIVE RATES ALONE
--
-- The only exact bridge currently connecting the R568 forcing-full vocabulary
-- to the R691 commutator is R687's PAIR-RATE-LIFT:
--
--   LiftedForcingFull = 8 * W(M,C).
--
-- R726 would need a one-sided transport from the R691/combined scalar to the
-- literal R406 remainder.  A tempting shortcut is to use positivity of the
-- physical viscous rates to compare the unlifted and rate-lifted forcing
-- squares.
--
-- R680 already gives the decisive algebraic firewall: positive rates and
-- positive coherent self-work do not fix the sign of the corresponding
-- rate-weighted coherent work.  Therefore no proof of the R726 transport may
-- cite rate positivity + coherent positivity as its sole mechanism.
--
-- This is scoped.  It does NOT refute R726 on literal NS trajectories; it says
-- additional physical signed/cancellation structure is required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNR650RateKernelPositiveRateNoGoRound680Exact as R680
import DASHI.Physics.Closure.NSTriadKNR650RateLiftedR568ToC2CommutatorRound687Exact as R687
import DASHI.Physics.Closure.NSTriadKNR650CombinedToLiteralR406Round726Exact as R726

round729PairRateLiftBridgeAvailable : Bool
round729PairRateLiftBridgeAvailable =
  R687.round687RateLiftedR568ForcingFullIsEightC2CommutatorWork

round729PositiveRatesAloneForceNeededTransportSign : Bool
round729PositiveRatesAloneForceNeededTransportSign =
  R680.round680PositiveRatesAloneForceFavorableWeightedWorkSign

round729PositiveRatesAndPositiveSelfWorkForceNeededTransportSign : Bool
round729PositiveRatesAndPositiveSelfWorkForceNeededTransportSign =
  R680.round680PositiveRatesAndPositiveSelfWorkForceFavorableWeightedWorkSign

round729AdditionalPhysicalSignedStructureRequired : Bool
round729AdditionalPhysicalSignedStructureRequired =
  R680.round680AdditionalPhysicalStructureNeeded

round729CombinedToR406TransportClosed : Bool
round729CombinedToR406TransportClosed =
  R726.round726CombinedToR406TransportClosed

round729ClaimsLiteralNSTransportImpossible : Bool
round729ClaimsLiteralNSTransportImpossible = false

round729IntroducesEstimate : Bool
round729IntroducesEstimate = false

round729ClayPromotion : Bool
round729ClayPromotion = false

round729PairRateLiftBridgeAvailableIsTrue :
  round729PairRateLiftBridgeAvailable ≡ true
round729PairRateLiftBridgeAvailableIsTrue =
  R687.round687RateLiftedR568ForcingFullIsEightC2CommutatorWorkIsTrue

round729PositiveRatesAloneForceNeededTransportSignIsFalse :
  round729PositiveRatesAloneForceNeededTransportSign ≡ false
round729PositiveRatesAloneForceNeededTransportSignIsFalse =
  R680.round680PositiveRatesAloneForceFavorableWeightedWorkSignIsFalse

round729PositiveRatesAndPositiveSelfWorkForceNeededTransportSignIsFalse :
  round729PositiveRatesAndPositiveSelfWorkForceNeededTransportSign ≡ false
round729PositiveRatesAndPositiveSelfWorkForceNeededTransportSignIsFalse =
  R680.round680PositiveRatesAndPositiveSelfWorkForceFavorableWeightedWorkSignIsFalse

round729AdditionalPhysicalSignedStructureRequiredIsTrue :
  round729AdditionalPhysicalSignedStructureRequired ≡ true
round729AdditionalPhysicalSignedStructureRequiredIsTrue =
  R680.round680AdditionalPhysicalStructureNeededIsTrue

round729CombinedToR406TransportClosedIsFalse :
  round729CombinedToR406TransportClosed ≡ false
round729CombinedToR406TransportClosedIsFalse =
  R726.round726CombinedToR406TransportClosedIsFalse

round729ClaimsLiteralNSTransportImpossibleIsFalse :
  round729ClaimsLiteralNSTransportImpossible ≡ false
round729ClaimsLiteralNSTransportImpossibleIsFalse = refl

round729IntroducesEstimateIsFalse :
  round729IntroducesEstimate ≡ false
round729IntroducesEstimateIsFalse = refl

round729ClayPromotionIsFalse :
  round729ClayPromotion ≡ false
round729ClayPromotionIsFalse = refl
