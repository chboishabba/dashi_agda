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

fullBoundaryNerveObstructionPaid :
  Nongin.fullBoundaryNerveObstructionPaid boundary ≡ true
fullBoundaryNerveObstructionPaid = refl

selectedProperBoundaryComparisonPaid :
  Nongin.selectedProperBoundaryComparisonPaid boundary ≡ true
selectedProperBoundaryComparisonPaid = refl

setLevelEffectiveDescentPaid :
  Nongin.setLevelEffectiveDescentPaid boundary ≡ true
setLevelEffectiveDescentPaid = refl

observationalGlobalUniquenessPaid :
  Nongin.observationalGlobalUniquenessPaid boundary ≡ true
observationalGlobalUniquenessPaid = refl

siteTransportCoverageObstructionPaid :
  Nongin.siteTransportCoverageObstructionPaid boundary ≡ true
siteTransportCoverageObstructionPaid = refl

empiricalTenPercentLawStillFalse :
  Nongin.empiricalTenPercentLawPromoted boundary ≡ false
empiricalTenPercentLawStillFalse = refl

fullBoundaryNerveStillFalse :
  Nongin.fullBoundaryNerveEquivalencePaid boundary ≡ false
fullBoundaryNerveStillFalse = refl

higherStackStillOpen : Nongin.certifiedHigherStackPaid boundary ≡ false
higherStackStillOpen = refl

hypersheafStillOpen : Nongin.certifiedHypersheafPaid boundary ≡ false
hypersheafStillOpen = refl
