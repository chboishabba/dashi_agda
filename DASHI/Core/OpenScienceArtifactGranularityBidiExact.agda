module DASHI.Core.OpenScienceArtifactGranularityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.OpenScienceKnowledgeReleaseBidiExact as O

------------------------------------------------------------------------
-- OPEN-SCIENCE ARTIFACT GRANULARITY
--
-- A public technical description is not the same evidence object as a public
-- implementation.  This refinement prevents 'the paper documents the code'
-- from silently becoming 'the source code was openly released'.
------------------------------------------------------------------------

data ArtifactExposureClass : Set where
  publicConceptDescription
  publicMethodDescription
  publicBenchmarkDisclosure
  publicDataRelease
  publicSourceCodeRelease
  publicBuildOrReproductionInstructions
  unresolvedArtifactExposure
  : ArtifactExposureClass

record ArtifactExposureReceipt : Set where
  constructor artifact-exposure-receipt
  field
    personOrProject : String
    exposure : ArtifactExposureClass
    sourceReference : String
    boundedReading : String

open ArtifactExposureReceipt public

record SourceCodeReleaseReceipt (receipt : ArtifactExposureReceipt) : Set where
  constructor source-code-release-receipt
  field
    correctExposure : exposure receipt ≡ publicSourceCodeRelease
    repositoryOrArchiveReference : String
    versionOrCommitReference : String
    licenceReference : String

open SourceCodeReleaseReceipt public

record MethodDisclosureWithoutSourceRelease
    (method benchmark : ArtifactExposureReceipt) : Set where
  constructor method-disclosure-without-source-release
  field
    methodIsPublic : exposure method ≡ publicMethodDescription
    benchmarkIsPublic : exposure benchmark ≡ publicBenchmarkDisclosure
    sourceReleaseNotPromoted : Bool
    sourceReleaseNotPromotedIsTrue : sourceReleaseNotPromoted ≡ true

open MethodDisclosureWithoutSourceRelease public

record ArtifactGranularityBoundary : Set where
  constructor artifact-granularity-boundary
  field
    methodDisclosureImpliesSourceCodeRelease : Bool
    methodDisclosureImpliesSourceCodeReleaseIsFalse :
      methodDisclosureImpliesSourceCodeRelease ≡ false
    benchmarkDisclosureImpliesSourceCodeRelease : Bool
    benchmarkDisclosureImpliesSourceCodeReleaseIsFalse :
      benchmarkDisclosureImpliesSourceCodeRelease ≡ false
    publicationImpliesOpenSourceLicence : Bool
    publicationImpliesOpenSourceLicenceIsFalse :
      publicationImpliesOpenSourceLicence ≡ false
    publicUsePermittedImpliesPreviouslyRestricted : Bool
    publicUsePermittedImpliesPreviouslyRestrictedIsFalse :
      publicUsePermittedImpliesPreviouslyRestricted ≡ false

canonicalArtifactGranularityBoundary : ArtifactGranularityBoundary
canonicalArtifactGranularityBoundary = artifact-granularity-boundary
  false refl
  false refl
  false refl
  false refl
