module DASHI.Reasoning.TrialecticHigherDescentMaxCutPromotionValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticHigherDescentMaxCutPromotionExact as Max

boundary : Max.TrialecticHigherDescentMaxCutBoundary
boundary = Max.canonicalTrialecticHigherDescentMaxCutBoundary

fullSiteGroupoid : Max.fullSiteNonDiscreteGroupoidPresheafPaid boundary ≡ true
fullSiteGroupoid = refl

pseudofunctor : Max.restrictionPseudofunctorPaid boundary ≡ true
pseudofunctor = refl

siteWideC3 : Max.siteWideC3EquivariancePaid boundary ≡ true
siteWideC3 = refl

generalTwoCells : Max.generalPhaseTwoCellsPaid boundary ≡ true
generalTwoCells = refl

generalCocycle : Max.arbitraryTriadicCocyclePaid boundary ≡ true
generalCocycle = refl

morphismDescent : Max.effectiveMorphismDescentPaid boundary ≡ true
morphismDescent = refl

typedIsoUniqueness : Max.uniquenessUpToTypedIsoPaid boundary ≡ true
typedIsoUniqueness = refl

allDepthWithPolicy : Max.policyIndexedAllDepthIterationPaid boundary ≡ true
allDepthWithPolicy = refl

effectiveStack : Max.certifiedEffectiveStackPaid boundary ≡ true
effectiveStack = refl

higherStack : Max.certifiedHigherStackPaid boundary ≡ true
higherStack = refl

siteNerveDepthTwo :
  Max.siteNondegenerateNerveDimensionAtMostTwoPaid boundary ≡ true
siteNerveDepthTwo = refl

finiteHyperdescent : Max.finiteOneTruncatedHyperdescentPaid boundary ≡ true
finiteHyperdescent = refl

finiteTriadicHypersheaf :
  Max.certifiedFiniteTriadicHypersheafPaid boundary ≡ true
finiteTriadicHypersheaf = refl

arbitraryInfinityHypercoverStillSeparate :
  Max.arbitraryInfinityHypercoverDescentPaid boundary ≡ false
arbitraryInfinityHypercoverStillSeparate = refl

arbitraryInfinityHypersheafStillSeparate :
  Max.certifiedArbitraryInfinityHypersheafPaid boundary ≡ false
arbitraryInfinityHypersheafStillSeparate = refl
