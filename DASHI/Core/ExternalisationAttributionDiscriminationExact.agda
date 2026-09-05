module DASHI.Core.ExternalisationAttributionDiscriminationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificWorkAttributionExact as A
import DASHI.Core.TechnicalExternalisationDepthBidiExact as X

------------------------------------------------------------------------
-- EXTERNALISATION ATTRIBUTION DISCRIMINATION
--
-- A deeply externalised multi-author artifact can establish that the artifact
-- is public and technically deep.  It does not by itself establish which named
-- contributor personally caused, advocated or uniquely drove the release.
------------------------------------------------------------------------

record SharedExternalisedArtifact : Set where
  constructor shared-externalised-artifact
  field
    artifact : X.TechnicalExternalisationProfile
    contributorCountLowerBound : Nat
    artifactReference : String

open SharedExternalisedArtifact public

record PersonArtifactAttribution : Set where
  constructor person-artifact-attribution
  field
    attribution : A.ScientificWorkAttribution
    sharedArtifact : SharedExternalisedArtifact
    boundedAttributionReference : String

open PersonArtifactAttribution public

record PersonSpecificExternalisationPressure
    (personArtifact : PersonArtifactAttribution) : Set where
  constructor person-specific-externalisation-pressure
  field
    roleSpecificReleaseActionReference : String
    personSpecificAdvocacyOrDecisionReference : String
    comparatorReference : String

open PersonSpecificExternalisationPressure public

record ExternalisationAttributionBoundary : Set where
  constructor externalisation-attribution-boundary
  field
    namedCoauthorMeansUniqueExternaliser : Bool
    namedCoauthorMeansUniqueExternaliserIsFalse :
      namedCoauthorMeansUniqueExternaliser ≡ false
    namedCoinventorMeansUniqueExternaliser : Bool
    namedCoinventorMeansUniqueExternaliserIsFalse :
      namedCoinventorMeansUniqueExternaliser ≡ false
    sharedDeepArtifactMeansAllContributorsHaveSameReleaseAgency : Bool
    sharedDeepArtifactMeansAllContributorsHaveSameReleaseAgencyIsFalse :
      sharedDeepArtifactMeansAllContributorsHaveSameReleaseAgency ≡ false
    personSpecificSelectionFeatureNeedsRoleSpecificReleaseEvidence : Bool
    personSpecificSelectionFeatureNeedsRoleSpecificReleaseEvidenceIsTrue :
      personSpecificSelectionFeatureNeedsRoleSpecificReleaseEvidence ≡ true

canonicalExternalisationAttributionBoundary : ExternalisationAttributionBoundary
canonicalExternalisationAttributionBoundary = externalisation-attribution-boundary
  false refl
  false refl
  false refl
  true refl
