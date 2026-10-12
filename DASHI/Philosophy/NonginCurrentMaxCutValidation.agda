module DASHI.Philosophy.NonginCurrentMaxCutValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Philosophy.NonginCurrentMaxCutExact as Nongin

boundary : Nongin.NonginCurrentMaxCutBoundary
boundary = Nongin.canonicalNonginCurrentMaxCutBoundary

consumerRelativeCorePaid : Nongin.consumerRelativeCorePaid boundary ≡ true
consumerRelativeCorePaid = refl

recursiveObserverReopeningPaid :
  Nongin.recursiveObserverReopeningPaid boundary ≡ true
recursiveObserverReopeningPaid = refl

localComplementFactorizationPaid :
  Nongin.localComplementFactorizationPaid boundary ≡ true
localComplementFactorizationPaid = refl

selectedCornerStarPaid : Nongin.selectedCornerStarPaid boundary ≡ true
selectedCornerStarPaid = refl

empiricalTenPercentLawStillFalse :
  Nongin.empiricalTenPercentLawPromoted boundary ≡ false
empiricalTenPercentLawStillFalse = refl

fullBoundaryNerveStillOpen :
  Nongin.fullBoundaryNerveEquivalencePaid boundary ≡ false
fullBoundaryNerveStillOpen = refl

higherStackStillOpen : Nongin.certifiedHigherStackPaid boundary ≡ false
higherStackStillOpen = refl

hypersheafStillOpen : Nongin.certifiedHypersheafPaid boundary ≡ false
hypersheafStillOpen = refl
