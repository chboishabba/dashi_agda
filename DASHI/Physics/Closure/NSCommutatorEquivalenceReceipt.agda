module DASHI.Physics.Closure.NSCommutatorEquivalenceReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSHighLowCommutatorObstructionReceipt
  as Commutator

------------------------------------------------------------------------
-- NS commutator equivalence.
--
-- Sprint 5 NS receipt.  It records that the HighLow commutator control
-- target is equivalent in strength to low-mode Lipschitz control / blowup
-- prevention, and therefore remains the Clay core rather than a shortcut.

data NSCommutatorEquivalenceStatus : Set where
  nsCommutatorEquivalenceRecorded_noPromotion :
    NSCommutatorEquivalenceStatus

data NSCommutatorEquivalenceFact : Set where
  commutatorReductionEstablished :
    NSCommutatorEquivalenceFact

  commutatorLipschitzEquivalentToBlowupPrevention :
    NSCommutatorEquivalenceFact

  bernsteinRouteCircular :
    NSCommutatorEquivalenceFact

  enstrophyRouteCircular :
    NSCommutatorEquivalenceFact

  besovRouteCircular :
    NSCommutatorEquivalenceFact

  kMinusHalfClaimRetracted :
    NSCommutatorEquivalenceFact

canonicalNSCommutatorEquivalenceFacts :
  List NSCommutatorEquivalenceFact
canonicalNSCommutatorEquivalenceFacts =
  commutatorReductionEstablished
  ∷ commutatorLipschitzEquivalentToBlowupPrevention
  ∷ bernsteinRouteCircular
  ∷ enstrophyRouteCircular
  ∷ besovRouteCircular
  ∷ kMinusHalfClaimRetracted
  ∷ []

data NSCommutatorEquivalencePromotion : Set where

nsCommutatorEquivalencePromotionImpossibleHere :
  NSCommutatorEquivalencePromotion →
  ⊥
nsCommutatorEquivalencePromotionImpossibleHere ()

nsCommutatorEquivalenceText : String
nsCommutatorEquivalenceText =
  "CommutatorLipschitzControl is equivalent to bounding ||grad u_<K||_LInfinity, hence to the no-finite-time-blowup control needed for Clay NS."

nsCommutatorEquivalenceBoundary : String
nsCommutatorEquivalenceBoundary =
  "This receipt records the equivalence and circularity audit only. It does not prove CommutatorLipschitzControl, cumulative dominance, K* no-drift, H118 continuation, or Clay NS."

record NSCommutatorEquivalenceReceipt : Setω where
  field
    status :
      NSCommutatorEquivalenceStatus

    statusIsCanonical :
      status ≡ nsCommutatorEquivalenceRecorded_noPromotion

    commutatorReceipt :
      Commutator.NSHighLowCommutatorObstructionReceipt

    commutatorReductionRecorded :
      Commutator.highLowEqualsCommutatorRecorded commutatorReceipt ≡ true

    commutatorStillOpen :
      Commutator.commutatorLipschitzControlProved commutatorReceipt ≡ false

    previousClayStillFalse :
      Commutator.clayNavierStokesPromoted commutatorReceipt ≡ false

    facts :
      List NSCommutatorEquivalenceFact

    factsAreCanonical :
      facts ≡ canonicalNSCommutatorEquivalenceFacts

    commutatorLipschitzEquivalentToBlowupPreventionRecorded :
      Bool

    commutatorLipschitzEquivalentToBlowupPreventionRecordedIsTrue :
      commutatorLipschitzEquivalentToBlowupPreventionRecorded ≡ true

    bernsteinRouteCircularRecorded :
      Bool

    bernsteinRouteCircularRecordedIsTrue :
      bernsteinRouteCircularRecorded ≡ true

    enstrophyRouteCircularRecorded :
      Bool

    enstrophyRouteCircularRecordedIsTrue :
      enstrophyRouteCircularRecorded ≡ true

    besovRouteCircularRecorded :
      Bool

    besovRouteCircularRecordedIsTrue :
      besovRouteCircularRecorded ≡ true

    kMinusHalfClaimRetractedRecorded :
      Bool

    kMinusHalfClaimRetractedRecordedIsTrue :
      kMinusHalfClaimRetractedRecorded ≡ true

    highLowBoundAccepted :
      Bool

    highLowBoundAcceptedIsFalse :
      highLowBoundAccepted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSCommutatorEquivalencePromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSCommutatorEquivalencePromotion →
      ⊥

    equivalenceText :
      String

    equivalenceTextIsCanonical :
      equivalenceText ≡ nsCommutatorEquivalenceText

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ nsCommutatorEquivalenceBoundary

open NSCommutatorEquivalenceReceipt public

canonicalNSCommutatorEquivalenceReceipt :
  NSCommutatorEquivalenceReceipt
canonicalNSCommutatorEquivalenceReceipt =
  record
    { status =
        nsCommutatorEquivalenceRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; commutatorReceipt =
        Commutator.canonicalNSHighLowCommutatorObstructionReceipt
    ; commutatorReductionRecorded =
        refl
    ; commutatorStillOpen =
        refl
    ; previousClayStillFalse =
        refl
    ; facts =
        canonicalNSCommutatorEquivalenceFacts
    ; factsAreCanonical =
        refl
    ; commutatorLipschitzEquivalentToBlowupPreventionRecorded =
        true
    ; commutatorLipschitzEquivalentToBlowupPreventionRecordedIsTrue =
        refl
    ; bernsteinRouteCircularRecorded =
        true
    ; bernsteinRouteCircularRecordedIsTrue =
        refl
    ; enstrophyRouteCircularRecorded =
        true
    ; enstrophyRouteCircularRecordedIsTrue =
        refl
    ; besovRouteCircularRecorded =
        true
    ; besovRouteCircularRecordedIsTrue =
        refl
    ; kMinusHalfClaimRetractedRecorded =
        true
    ; kMinusHalfClaimRetractedRecordedIsTrue =
        refl
    ; highLowBoundAccepted =
        false
    ; highLowBoundAcceptedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        nsCommutatorEquivalencePromotionImpossibleHere
    ; equivalenceText =
        nsCommutatorEquivalenceText
    ; equivalenceTextIsCanonical =
        refl
    ; boundary =
        nsCommutatorEquivalenceBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalNSCommutatorEquivalenceKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSCommutatorEquivalenceReceipt ≡ false
canonicalNSCommutatorEquivalenceKeepsClayFalse =
  refl
