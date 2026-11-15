module DASHI.Reasoning.TrialecticT27FiniteTriadicHypersheafValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27FiniteTriadicHypersheafExact as Hyper27

policy : Tower.T27CompletionPolicy
policy = Tower.firstNine

boundary : Hyper27.TrialecticT27FiniteTriadicHypersheafBoundary
boundary = Hyper27.canonicalTrialecticT27FiniteTriadicHypersheafBoundary

coverClassifierReused : Hyper27.relationalCoverTopologyReused boundary ≡ true
coverClassifierReused = refl

graphObjectDescentPaid : Hyper27.completedT27ObjectHyperdescentPaid boundary ≡ true
graphObjectDescentPaid = refl

graphMorphismDescentPaid : Hyper27.completedT27MorphismHyperdescentPaid boundary ≡ true
graphMorphismDescentPaid = refl

twoSkeletonPaid : Hyper27.localPhaseTwoSkeletonCocyclePaid boundary ≡ true
twoSkeletonPaid = refl

siteDepthPaid : Hyper27.strictSiteDepthAtMostTwoReused boundary ≡ true
siteDepthPaid = refl

finiteHypersheafPaid : Hyper27.certifiedCompletedT27FiniteHypersheaf boundary ≡ true
finiteHypersheafPaid = refl

ambientNotHypersheaf : Hyper27.unconstrainedAmbientT27HypersheafClaimed boundary ≡ false
ambientNotHypersheaf = refl

arbitraryInfinityStillSeparate : Hyper27.certifiedArbitraryInfinityT27Hypersheaf boundary ≡ false
arbitraryInfinityStillSeparate = refl

canonicalCoverCertificate : Hyper27.T27CoverHyperdescentCertificate policy Site.triadicRelationalSieveCovers
canonicalCoverCertificate = Hyper27.t27HyperdescentForEveryCover policy Site.triadicRelationalSieveCovers
