module DASHI.Reasoning.Trialectic369FullBoundaryNerveComparisonValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.Trialectic369FullBoundaryNerveComparisonExact as Full

boundary : Full.Trialectic369FullBoundaryNerveComparisonBoundary
boundary = Full.canonicalTrialectic369FullBoundaryNerveComparisonBoundary

fullBoundaryCountsOwned : Full.fullBoundaryCountsOwned boundary ≡ true
fullBoundaryCountsOwned = refl

globalRankObstructionPaid : Full.globalRankObstructionPaid boundary ≡ true
globalRankObstructionPaid = refl

fullEquivalenceNotPaid : Full.rankPreservingFullEquivalencePaid boundary ≡ false
fullEquivalenceNotPaid = refl

selectedProperStarComparisonPaid :
  Full.selectedProperStarComparisonPaid boundary ≡ true
selectedProperStarComparisonPaid = refl

dyadicTripleStillEmpty : Full.literalDyadicTripleIntersectionInhabited boundary ≡ false
dyadicTripleStillEmpty = refl

augmentedTripleIsSeparate : Full.augmentedTripleAddedSeparately boundary ≡ true
augmentedTripleIsSeparate = refl
