module DASHI.Biology.Protein.TRPA1SourceAttributionEnvelopeValidation where

open import DASHI.Core.Prelude

import DASHI.Biology.Protein.TRPA1SourceAttributionEnvelopeExact as P

identityRegression :
  P.TRPA1SourceAttributionBoundary.doiRetained
    P.canonicalTRPA1SourceAttributionBoundary
  ≡ true
  × P.TRPA1SourceAttributionBoundary.pmidRetained
    P.canonicalTRPA1SourceAttributionBoundary
  ≡ true
  × P.TRPA1SourceAttributionBoundary.pmcidRetained
    P.canonicalTRPA1SourceAttributionBoundary
  ≡ true
  × P.TRPA1SourceAttributionBoundary.articleQidExplicitlyUnresolved
    P.canonicalTRPA1SourceAttributionBoundary
  ≡ true
identityRegression = refl , refl , refl , refl

attributionRegression :
  P.TRPA1SourceAttributionBoundary.reusesAttributedSourceCore
    P.canonicalTRPA1SourceAttributionBoundary
  ≡ true
  × P.TRPA1SourceAttributionBoundary.existingFengBiologyRetainedAsDonor
    P.canonicalTRPA1SourceAttributionBoundary
  ≡ true
  × P.TRPA1SourceAttributionBoundary.identityCreatesBiologicalClaim
    P.canonicalTRPA1SourceAttributionBoundary
  ≡ false
  × P.TRPA1SourceAttributionBoundary.citationImportsProofOrAuthority
    P.canonicalTRPA1SourceAttributionBoundary
  ≡ false
attributionRegression = refl , refl , refl , refl
