module DASHI.Physics.Closure.NSHighLowFluxControlAuditReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSCumulativeTailDominanceObstructionReceipt
  as Tail

------------------------------------------------------------------------
-- NS HighLow flux control audit.
--
-- Second NS worker receipt.  It retracts the claimed HighLow K^{-1/2}
-- suppression, records the exact transport cancellation, and isolates the
-- live obstruction as low-mode Lipschitz commutator control without imported
-- regularity.

data NSHighLowFluxControlAuditStatus : Set where
  nsHighLowFluxControlAuditRecorded_noPromotion :
    NSHighLowFluxControlAuditStatus

data NSHighLowAuditCheck : Set where
  highLowTrilinearFormWritten :
    NSHighLowAuditCheck

  derivativePlacementChecked :
    NSHighLowAuditCheck

  frequencyProjectionGainChecked :
    NSHighLowAuditCheck

  noHiddenLInfinityUseChecked :
    NSHighLowAuditCheck

  noGlobalH118InputChecked :
    NSHighLowAuditCheck

  commutatorCancellationChecked :
    NSHighLowAuditCheck

  transportTermVanishesChecked :
    NSHighLowAuditCheck

  kMinusHalfClaimRetractedChecked :
    NSHighLowAuditCheck

  correctGrowingBoundRecorded :
    NSHighLowAuditCheck

  lowModeLipschitzObstacleIsolated :
    NSHighLowAuditCheck

canonicalNSHighLowAuditChecks : List NSHighLowAuditCheck
canonicalNSHighLowAuditChecks =
  highLowTrilinearFormWritten
  ∷ derivativePlacementChecked
  ∷ frequencyProjectionGainChecked
  ∷ noHiddenLInfinityUseChecked
  ∷ noGlobalH118InputChecked
  ∷ commutatorCancellationChecked
  ∷ transportTermVanishesChecked
  ∷ kMinusHalfClaimRetractedChecked
  ∷ correctGrowingBoundRecorded
  ∷ lowModeLipschitzObstacleIsolated
  ∷ []

data NSHighLowAuditForbiddenInput : Set where
  globalLInfinityInput :
    NSHighLowAuditForbiddenInput

  serrinInput :
    NSHighLowAuditForbiddenInput

  bkmInput :
    NSHighLowAuditForbiddenInput

  globalH118Input :
    NSHighLowAuditForbiddenInput

  globalHOneHalfShortcut :
    NSHighLowAuditForbiddenInput

canonicalNSHighLowAuditForbiddenInputs :
  List NSHighLowAuditForbiddenInput
canonicalNSHighLowAuditForbiddenInputs =
  globalLInfinityInput
  ∷ serrinInput
  ∷ bkmInput
  ∷ globalH118Input
  ∷ globalHOneHalfShortcut
  ∷ []

data NSHighLowFluxControlAuditPromotion : Set where

nsHighLowFluxControlAuditPromotionImpossibleHere :
  NSHighLowFluxControlAuditPromotion →
  ⊥
nsHighLowFluxControlAuditPromotionImpossibleHere ()

highLowClaimedBoundText : String
highLowClaimedBoundText =
  "Retracted claim: HighLow flux has K^{-1/2} suppression against tail dissipation without hidden L_infinity, H^{1/2}, Serrin, BKM, or global H^{11/8} input."

highLowLiveObstructionText : String
highLowLiveObstructionText =
  "Live obstruction: prove CommutatorLipschitzControl for [P_{>K}, u_{<K}.grad]u_{>K} without hidden regularity, or produce a Leray-energy-bounded HighLow counterfamily where injection beats tail dissipation."

highLowTransportCancellationText : String
highLowTransportCancellationText =
  "<(u_<K . grad) u_>K, u_>K> = 0 by integration by parts and div u_<K = 0; the remaining HighLow term is the commutator only."

highLowCorrectBoundText : String
highLowCorrectBoundText =
  "Correct audit bound grows like C*2^K*sqrt(E0)/(nu^{1/2}*Diss_{>K}^{1/2}); the earlier K^{-1/2} suppression has no accepted derivation."

highLowAuditBoundaryText : String
highLowAuditBoundaryText =
  "This receipt accepts HighHigh absorption and exact transport cancellation, but it retracts the HighLow K^{-1/2} estimate and does not prove cumulative dominance, K* no-drift, CommutatorLipschitzControl, or Clay NS."

record NSHighLowFluxControlAuditReceipt : Setω where
  field
    status :
      NSHighLowFluxControlAuditStatus

    statusIsCanonical :
      status ≡ nsHighLowFluxControlAuditRecorded_noPromotion

    tailDominanceReceipt :
      Tail.NSCumulativeTailDominanceObstructionReceipt

    previousHighHighAbsorbed :
      Tail.highHighFluxAbsorbedHere tailDominanceReceipt ≡ true

    previousHighLowStillOpen :
      Tail.highLowFluxControlWithoutRegularityProved tailDominanceReceipt
      ≡
      false

    previousCumulativeDominanceStillOpen :
      Tail.cumulativeDominanceProvedHere tailDominanceReceipt ≡ false

    auditChecks :
      List NSHighLowAuditCheck

    auditChecksAreCanonical :
      auditChecks ≡ canonicalNSHighLowAuditChecks

    forbiddenInputs :
      List NSHighLowAuditForbiddenInput

    forbiddenInputsAreCanonical :
      forbiddenInputs ≡ canonicalNSHighLowAuditForbiddenInputs

    highHighAbsorbed :
      Bool

    highHighAbsorbedIsTrue :
      highHighAbsorbed ≡ true

    highLowClaimedBound :
      Set

    derivativePlacementCheckTarget :
      Set

    frequencyGainCheckTarget :
      Set

    noHiddenLInfinityUseTarget :
      Set

    noGlobalRegularityInput :
      Bool

    noGlobalRegularityInputIsTrue :
      noGlobalRegularityInput ≡ true

    commutatorCancellationAccepted :
      Bool

    commutatorCancellationAcceptedIsFalse :
      commutatorCancellationAccepted ≡ false

    transportTermVanishesExactly :
      Bool

    transportTermVanishesExactlyIsTrue :
      transportTermVanishesExactly ≡ true

    highLowEqualsCommutatorOnly :
      Bool

    highLowEqualsCommutatorOnlyIsTrue :
      highLowEqualsCommutatorOnly ≡ true

    kMinusHalfClaimRetracted :
      Bool

    kMinusHalfClaimRetractedIsTrue :
      kMinusHalfClaimRetracted ≡ true

    lowModeLipschitzControlledWithoutRegularity :
      Bool

    lowModeLipschitzControlledWithoutRegularityIsFalse :
      lowModeLipschitzControlledWithoutRegularity ≡ false

    highLowBoundAccepted :
      Bool

    highLowBoundAcceptedIsFalse :
      highLowBoundAccepted ≡ false

    highLowCounterfamilySearchRequired :
      Bool

    highLowCounterfamilySearchRequiredIsTrue :
      highLowCounterfamilySearchRequired ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSHighLowFluxControlAuditPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSHighLowFluxControlAuditPromotion →
      ⊥

    claimedBoundText :
      String

    claimedBoundTextIsCanonical :
      claimedBoundText ≡ highLowClaimedBoundText

    liveObstruction :
      String

    liveObstructionIsCanonical :
      liveObstruction ≡ highLowLiveObstructionText

    transportCancellation :
      String

    transportCancellationIsCanonical :
      transportCancellation ≡ highLowTransportCancellationText

    correctBound :
      String

    correctBoundIsCanonical :
      correctBound ≡ highLowCorrectBoundText

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ highLowAuditBoundaryText

open NSHighLowFluxControlAuditReceipt public

canonicalNSHighLowFluxControlAuditReceipt :
  NSHighLowFluxControlAuditReceipt
canonicalNSHighLowFluxControlAuditReceipt =
  record
    { status =
        nsHighLowFluxControlAuditRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; tailDominanceReceipt =
        Tail.canonicalNSCumulativeTailDominanceObstructionReceipt
    ; previousHighHighAbsorbed =
        refl
    ; previousHighLowStillOpen =
        refl
    ; previousCumulativeDominanceStillOpen =
        refl
    ; auditChecks =
        canonicalNSHighLowAuditChecks
    ; auditChecksAreCanonical =
        refl
    ; forbiddenInputs =
        canonicalNSHighLowAuditForbiddenInputs
    ; forbiddenInputsAreCanonical =
        refl
    ; highHighAbsorbed =
        true
    ; highHighAbsorbedIsTrue =
        refl
    ; highLowClaimedBound =
        ⊥
    ; derivativePlacementCheckTarget =
        ⊥
    ; frequencyGainCheckTarget =
        ⊥
    ; noHiddenLInfinityUseTarget =
        ⊥
    ; noGlobalRegularityInput =
        true
    ; noGlobalRegularityInputIsTrue =
        refl
    ; commutatorCancellationAccepted =
        false
    ; commutatorCancellationAcceptedIsFalse =
        refl
    ; transportTermVanishesExactly =
        true
    ; transportTermVanishesExactlyIsTrue =
        refl
    ; highLowEqualsCommutatorOnly =
        true
    ; highLowEqualsCommutatorOnlyIsTrue =
        refl
    ; kMinusHalfClaimRetracted =
        true
    ; kMinusHalfClaimRetractedIsTrue =
        refl
    ; lowModeLipschitzControlledWithoutRegularity =
        false
    ; lowModeLipschitzControlledWithoutRegularityIsFalse =
        refl
    ; highLowBoundAccepted =
        false
    ; highLowBoundAcceptedIsFalse =
        refl
    ; highLowCounterfamilySearchRequired =
        true
    ; highLowCounterfamilySearchRequiredIsTrue =
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
        nsHighLowFluxControlAuditPromotionImpossibleHere
    ; claimedBoundText =
        highLowClaimedBoundText
    ; claimedBoundTextIsCanonical =
        refl
    ; liveObstruction =
        highLowLiveObstructionText
    ; liveObstructionIsCanonical =
        refl
    ; transportCancellation =
        highLowTransportCancellationText
    ; transportCancellationIsCanonical =
        refl
    ; correctBound =
        highLowCorrectBoundText
    ; correctBoundIsCanonical =
        refl
    ; boundary =
        highLowAuditBoundaryText
    ; boundaryIsCanonical =
        refl
    }

canonicalNSHighLowBoundStillRejected :
  highLowBoundAccepted canonicalNSHighLowFluxControlAuditReceipt ≡ false
canonicalNSHighLowBoundStillRejected =
  refl
