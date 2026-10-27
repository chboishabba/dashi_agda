module DASHI.Unified.BalabanIbrahimParetoSnowballTOEValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact as Owner
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier

toeRecognitionParetoMatchesOwner :
  TOE.toeIbrahimRecognitionParetoBoundary
  ≡ Owner.ibrahimRecognitionParetoBoundary
toeRecognitionParetoMatchesOwner = refl

unifierRecognitionParetoMatchesOwner :
  Unifier.unifierIbrahimRecognitionParetoBoundary
  ≡ Owner.ibrahimRecognitionParetoBoundary
unifierRecognitionParetoMatchesOwner = refl

toeCharacterExecutionMatchesOwner :
  TOE.toeIbrahimCharacterExecutionFrontier
  ≡ Owner.ibrahimCharacterExecutionFrontier
toeCharacterExecutionMatchesOwner = refl

unifierCharacterExecutionMatchesOwner :
  Unifier.unifierIbrahimCharacterExecutionFrontier
  ≡ Owner.ibrahimCharacterExecutionFrontier
unifierCharacterExecutionMatchesOwner = refl

toeHZetaMaxCutMatchesOwner :
  TOE.toeIbrahimSchrodingerHZetaMaxCutBoundary
  ≡ Owner.ibrahimSchrodingerHZetaMaxCutBoundary
toeHZetaMaxCutMatchesOwner = refl

unifierHZetaMaxCutMatchesOwner :
  Unifier.unifierIbrahimSchrodingerHZetaMaxCutBoundary
  ≡ Owner.ibrahimSchrodingerHZetaMaxCutBoundary
unifierHZetaMaxCutMatchesOwner = refl

toeZKPFrameMatchesOwner :
  TOE.toeBalabanIbrahimParetoSnowballZKPFrame
  ≡ Owner.canonicalTOEZKPFrame
toeZKPFrameMatchesOwner = refl

unifierZKPFrameMatchesOwner :
  Unifier.unifierBalabanIbrahimParetoSnowballZKPFrame
  ≡ Owner.canonicalTOEZKPFrame
unifierZKPFrameMatchesOwner = refl

toeBalabanScaleTransferStillImpossible :
  Owner.BalabanScaleTransferPromotion → ⊥
toeBalabanScaleTransferStillImpossible =
  TOE.toeBalabanScaleTransferPromotionImpossible

unifierBalabanScaleTransferStillImpossible :
  Owner.BalabanScaleTransferPromotion → ⊥
unifierBalabanScaleTransferStillImpossible =
  Unifier.unifierBalabanScaleTransferPromotionImpossible
