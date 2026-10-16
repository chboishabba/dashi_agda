module DASHI.Reasoning.TrialecticFiniteTriadicHypersheafValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticFiniteTriadicHypersheafExact as Hyper

boundary : Hyper.TrialecticFiniteTriadicHypersheafBoundary
boundary = Hyper.canonicalTrialecticFiniteTriadicHypersheafBoundary

coverTopologyExhausted :
  Hyper.everyCoverIsMaximalOrTriadic boundary ≡ true
coverTopologyExhausted = refl

everyCoverHasCertificate :
  Hyper.everyCoverHasHyperdescentCertificate boundary ≡ true
everyCoverHasCertificate = refl

siteHasNoStrictThreeChain :
  Hyper.siteHasNoStrictThreeArrowChain boundary ≡ true
siteHasNoStrictThreeChain = refl

triadicPullbacksMaximal :
  Hyper.triadicNonGlobalPullbacksAreMaximal boundary ≡ true
triadicPullbacksMaximal = refl

objectHyperdescentPaid :
  Hyper.objectHyperdescentPaid boundary ≡ true
objectHyperdescentPaid = refl

morphismHyperdescentPaid :
  Hyper.morphismHyperdescentPaid boundary ≡ true
morphismHyperdescentPaid = refl

twoSkeletonCoherencePaid :
  Hyper.twoSkeletonCocyclePaid boundary ≡ true
twoSkeletonCoherencePaid = refl

higherMatchingStagesCollapse :
  Hyper.higherMatchingStagesMaximal boundary ≡ true
higherMatchingStagesCollapse = refl

finiteTriadicHypersheafCertified :
  Hyper.certifiedFiniteOneTruncatedHypersheaf boundary ≡ true
finiteTriadicHypersheafCertified = refl

arbitraryInfinityHypercoverStillSeparate :
  Hyper.certifiedArbitraryInfinityHypersheaf boundary ≡ false
arbitraryInfinityHypercoverStillSeparate = refl
