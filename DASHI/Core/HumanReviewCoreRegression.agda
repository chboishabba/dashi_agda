module DASHI.Core.HumanReviewCoreRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true)

import DASHI.Core.HumanReviewCore as Review

canonicalReview : Review.GenericHumanReviewReceipt
canonicalReview =
  Review.generic-human-review-receipt
    "review-receipt"
    "review-item"
    "reviewer"
    "observation"

canonicalBinding : Review.ExactReviewItemBinding
canonicalBinding =
  Review.exact-review-item-binding
    "source-manifestation"
    "candidate-pnf-batch"
    "candidate-factor"
    "consumer"
    true
    refl

bindingAcceptedOrQualified :
  Review.acceptedOrQualified canonicalBinding ≡ true
bindingAcceptedOrQualified =
  Review.acceptedOrQualifiedIsTrue canonicalBinding
