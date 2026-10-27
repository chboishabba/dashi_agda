{-# OPTIONS --safe #-}
module DASHI.Unified.GovernanceMaxCutParetoSnowballTOEConvergenceValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unified.GovernanceMaxCutParetoSnowballTOEConvergenceExact as Owner
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Unified.Everything as Unified

toeReceiptMatchesOwner :
  TOE.toeGovernanceMaxCutParetoSnowballReceipt
  ≡ Owner.canonicalGovernanceMaxCutParetoSnowballTOEReceipt
toeReceiptMatchesOwner = refl

unifierReceiptMatchesOwner :
  Unifier.unifierGovernanceMaxCutParetoSnowballReceipt
  ≡ Owner.canonicalGovernanceMaxCutParetoSnowballTOEReceipt
unifierReceiptMatchesOwner = refl

unifiedReceiptMatchesOwner :
  Unified.unifiedGovernanceMaxCutParetoSnowballReceipt
  ≡ Owner.canonicalGovernanceMaxCutParetoSnowballTOEReceipt
unifiedReceiptMatchesOwner = refl

toeFrameMatchesOwner :
  TOE.toeGovernanceMaxCutParetoSnowballZKPFrame
  ≡ Owner.canonicalGovernanceMaxCutParetoSnowballZKPFrame
toeFrameMatchesOwner = refl

unifierFrameMatchesOwner :
  Unifier.unifierGovernanceMaxCutParetoSnowballZKPFrame
  ≡ Owner.canonicalGovernanceMaxCutParetoSnowballZKPFrame
unifierFrameMatchesOwner = refl

unifiedFrameMatchesOwner :
  Unified.unifiedGovernanceMaxCutParetoSnowballZKPFrame
  ≡ Owner.canonicalGovernanceMaxCutParetoSnowballZKPFrame
unifiedFrameMatchesOwner = refl

toeBalabanPromotionStillImpossible :
  Owner.BalabanScaleTransferPromotion → ⊥
toeBalabanPromotionStillImpossible =
  TOE.toeGovernanceMaxCutBalabanScaleTransferImpossible

unifierBalabanPromotionStillImpossible :
  Owner.BalabanScaleTransferPromotion → ⊥
unifierBalabanPromotionStillImpossible =
  Unifier.unifierGovernanceMaxCutBalabanScaleTransferImpossible

unifiedBalabanPromotionStillImpossible :
  Owner.BalabanScaleTransferPromotion → ⊥
unifiedBalabanPromotionStillImpossible =
  Unified.unifiedGovernanceMaxCutBalabanScaleTransferImpossible

toeIbrahimSearchPriorityStillNotProof :
  Owner.SearchPriorityCreatesProof → ⊥
toeIbrahimSearchPriorityStillNotProof =
  TOE.toeGovernanceMaxCutIbrahimSearchPriorityNotProof

unifierIbrahimSearchPriorityStillNotProof :
  Owner.SearchPriorityCreatesProof → ⊥
unifierIbrahimSearchPriorityStillNotProof =
  Unifier.unifierGovernanceMaxCutIbrahimSearchPriorityNotProof

unifiedIbrahimSearchPriorityStillNotProof :
  Owner.SearchPriorityCreatesProof → ⊥
unifiedIbrahimSearchPriorityStillNotProof =
  Unified.unifiedGovernanceMaxCutIbrahimSearchPriorityNotProof

selected3BCoreFlagStillFalse :
  Owner.selected3BCoreStillOpen
    Owner.canonicalGovernanceMaxCutParetoSnowballTOEReceipt
  ≡ false
selected3BCoreFlagStillFalse =
  Owner.selected3BCoreRemainsOpen

selected3BActionFlagStillFalse :
  Owner.selected3BActionStillOpen
    Owner.canonicalGovernanceMaxCutParetoSnowballTOEReceipt
  ≡ false
selected3BActionFlagStillFalse =
  Owner.selected3BActionRemainsOpen

esdMutationStillFalse :
  Owner.esdMutationAllowed
    Owner.canonicalGovernanceMaxCutParetoSnowballTOEReceipt
  ≡ false
esdMutationStillFalse =
  Owner.esdRemainsReadOnly
