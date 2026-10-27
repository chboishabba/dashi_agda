{-# OPTIONS --safe #-}
module DASHI.Unified.NavierStokesABCDTerminalTOEValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false)

import DASHI.Unified.NavierStokesABCDTerminalTOEExact as Terminal
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Unified.Everything as Unified

toeReceiptMatchesCanonical :
  TOE.toeNavierStokesABCDTerminalReceipt
  ≡ Terminal.canonicalNSABCDTerminalTOEReceipt
toeReceiptMatchesCanonical = refl

unifierReceiptMatchesCanonical :
  Unifier.unifierNavierStokesABCDTerminalReceipt
  ≡ Terminal.canonicalNSABCDTerminalTOEReceipt
unifierReceiptMatchesCanonical = refl

unifiedReceiptMatchesCanonical :
  Unified.unifiedNavierStokesABCDTerminalReceipt
  ≡ Terminal.canonicalNSABCDTerminalTOEReceipt
unifiedReceiptMatchesCanonical = refl

toeReserveRemainsOpen :
  Terminal.bReserveEstimateClosed Terminal.canonicalNSABCDTerminalTOEReceipt
  ≡ false
toeReserveRemainsOpen = Terminal.toeBReserveStillOpen

toeW1RemainsOpen :
  Terminal.bW1Closed Terminal.canonicalNSABCDTerminalTOEReceipt
  ≡ false
toeW1RemainsOpen = Terminal.toeBW1StillOpen

toeContinuationRemainsOpen :
  Terminal.bContinuationClosed Terminal.canonicalNSABCDTerminalTOEReceipt
  ≡ false
toeContinuationRemainsOpen = Terminal.toeBContinuationStillOpen

toeSelectedRateDecisionRemainsOpen :
  Terminal.bSelectedRateDecisionClosed
    Terminal.canonicalNSABCDTerminalTOEReceipt
  ≡ false
toeSelectedRateDecisionRemainsOpen =
  Terminal.toeBSelectedRateDecisionStillOpen

toeESDMutationDisabled :
  Terminal.NSABCDTerminalZKPFrame.esdMutationAllowed
    Terminal.canonicalNSABCDTerminalZKPFrame
  ≡ false
toeESDMutationDisabled = refl

toeClayPromotionDisabled :
  Terminal.NSABCDTerminalZKPFrame.createsClayPromotion
    Terminal.canonicalNSABCDTerminalZKPFrame
  ≡ false
toeClayPromotionDisabled = refl

toeBalabanContinuumPromotionDisabled :
  Terminal.NSABCDTerminalZKPFrame.createsBalabanContinuumPromotion
    Terminal.canonicalNSABCDTerminalZKPFrame
  ≡ false
toeBalabanContinuumPromotionDisabled = refl

toeMonsterRecognitionDisabled :
  Terminal.NSABCDTerminalZKPFrame.createsMonsterRecognition
    Terminal.canonicalNSABCDTerminalZKPFrame
  ≡ false
toeMonsterRecognitionDisabled = refl
