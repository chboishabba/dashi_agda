{-# OPTIONS --safe #-}
module DASHI.Unified.TOECurrentMaxCutHyperfabricValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unified.TOECurrentMaxCutHyperfabricExact as Owner
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Unified.Everything as Unified

toeReceiptMatchesOwner :
  TOE.toeCurrentMaxCutHyperfabricReceipt
  ≡ Owner.canonicalTOECurrentMaxCutHyperfabricReceipt
toeReceiptMatchesOwner = refl

unifierReceiptMatchesOwner :
  Unifier.unifierCurrentMaxCutHyperfabricReceipt
  ≡ Owner.canonicalTOECurrentMaxCutHyperfabricReceipt
unifierReceiptMatchesOwner = refl

unifiedReceiptMatchesOwner :
  Unified.unifiedCurrentMaxCutHyperfabricReceipt
  ≡ Owner.canonicalTOECurrentMaxCutHyperfabricReceipt
unifiedReceiptMatchesOwner = refl

toeNineCountMatchesOwner :
  TOE.toeCurrentHyperformNineCount ≡ Owner.currentHyperformNineCount
toeNineCountMatchesOwner = refl

toeTwentySevenCountMatchesOwner :
  TOE.toeCurrentHyperformTwentySevenCount
  ≡ Owner.currentHyperformTwentySevenCount
toeTwentySevenCountMatchesOwner = refl

toeEightyOneCountMatchesOwner :
  TOE.toeCurrentHyperformEightyOneCount
  ≡ Owner.currentHyperformEightyOneCount
toeEightyOneCountMatchesOwner = refl

toePadicPrefixLossMatchesOwner :
  Owner.PadicPrefixRecovery → ⊥
toePadicPrefixLossMatchesOwner =
  TOE.toeCurrentPadicPrefixCannotRecoverDiscardedDigit

unifierPadicPrefixLossMatchesOwner :
  Owner.PadicPrefixRecovery → ⊥
unifierPadicPrefixLossMatchesOwner =
  Unifier.unifierCurrentPadicPrefixCannotRecoverDiscardedDigit

toeStreamPrefixLossMatchesOwner :
  Owner.StreamThirdPrefixRecovery → ⊥
toeStreamPrefixLossMatchesOwner =
  TOE.toeCurrentTwoDigitStreamCannotRecoverThird

unifierStreamPrefixLossMatchesOwner :
  Owner.StreamThirdPrefixRecovery → ⊥
unifierStreamPrefixLossMatchesOwner =
  Unifier.unifierCurrentTwoDigitStreamCannotRecoverThird

toeFleetGate4SameObjectStillBlocked :
  Owner.Current.Fleet58IsGate4SameObject → ⊥
toeFleetGate4SameObjectStillBlocked =
  TOE.toeCurrentFleet58DoesNotBecomeGate4SameObject

unifierFleetGate4SameObjectStillBlocked :
  Owner.Current.Fleet58IsGate4SameObject → ⊥
unifierFleetGate4SameObjectStillBlocked =
  Unifier.unifierCurrentFleet58DoesNotBecomeGate4SameObject
