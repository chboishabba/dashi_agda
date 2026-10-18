module DASHI.Wikimedia.MaboReviewedContextFederationValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Wikimedia.MaboReviewedContextFederationExact as Federation

providerPaid : Federation.wikidataRevisionPinnedProviderPaid Federation.canonicalBoundary ≡ true
providerPaid = refl

reviewRequired : Federation.explicitCandidateReviewRequired Federation.canonicalBoundary ≡ true
reviewRequired = refl

unreviewedDoesNotMaterialise : Federation.unreviewedCandidateMaterialises Federation.canonicalBoundary ≡ false
unreviewedDoesNotMaterialise = refl

contextDoesNotCreateAuthority : Federation.reviewedContextCreatesSemanticAuthority Federation.canonicalBoundary ≡ false
contextDoesNotCreateAuthority = refl

contextDoesNotCreateLegalIRSupport : Federation.reviewedContextCreatesLegalIRSupport Federation.canonicalBoundary ≡ false
contextDoesNotCreateLegalIRSupport = refl

p4006StillCandidateOnly : Federation.p4006AuthoritySourceCandidateCreatesAuthority ≡ false
p4006StillCandidateOnly = refl

applicabilityNotPromoted : Federation.applicabilityPromoted Federation.canonicalBoundary ≡ false
applicabilityNotPromoted = refl

truthNotPromoted : Federation.claimTruthPromoted Federation.canonicalBoundary ≡ false
truthNotPromoted = refl

walkerRemainsNetworkFree : Federation.walkerPerformsNetworkIO Federation.canonicalBoundary ≡ false
walkerRemainsNetworkFree = refl
