module DASHI.Core.FormalizationRecoverySourceRegistryExact where

------------------------------------------------------------------------
-- FORMALIZATION / CLAIM-TRANSPORT SOURCE REGISTRY
--
-- Machine-readable provenance for the generic recovery / claim-transport lane.
-- These sources calibrate distinctions and terminology.  They are not imported
-- as proof authority for the local Agda theorems.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Provenance roles and identifier status.
------------------------------------------------------------------------

data CalibrationRole : Set where
  formalizationRecovery : CalibrationRole
  representationTranslation : CalibrationRole
  consistencyMetatheory : CalibrationRole

data IdentifierStatus : Set where
  verifiedDOI : IdentifierStatus
  stableArchiveIdentifier : IdentifierStatus
  repositoryPermanentIdentifier : IdentifierStatus
  journalDOINotYetVerified : IdentifierStatus

record CalibrationSource : Set where
  constructor calibrationSource
  field
    author : String
    title : String
    year : Nat
    venue : String
    stableIdentifier : String
    role : CalibrationRole
    identifierStatus : IdentifierStatus

open CalibrationSource public

------------------------------------------------------------------------
-- Sources.
------------------------------------------------------------------------

aspertNaiboSacerdotiCoen2026 : CalibrationSource
aspertNaiboSacerdotiCoen2026 =
  calibrationSource
    "Andrea Asperti; Alberto Naibo; Claudio Sacerdoti Coen"
    "Thinking Machines: Mathematical Reasoning in the Age of LLMs"
    2026
    "arXiv preprint; supplied manuscript also carries provisional journal metadata"
    "arxiv:2508.00459v2"
    formalizationRecovery
    stableArchiveIdentifier

-- The supplied manuscript displays `10.3390/bdcc1010000` while its publication
-- metadata is visibly unfinished.  Do not silently promote that string to a
-- verified final DOI.  The arXiv identifier above is the stable handle here.

wagner2019 : CalibrationSource
wagner2019 =
  calibrationSource
    "Roy Wagner"
    "Mathematical Abstraction as Unstable Translation Between Concrete Presentations"
    2019
    "Philosophy of Mathematics Education Journal 35; ETH Research Collection"
    "doi:10.3929/ethz-b-000387100"
    representationTranslation
    repositoryPermanentIdentifier

chow2018 : CalibrationSource
chow2018 =
  calibrationSource
    "Timothy Y. Chow"
    "The Consistency of Arithmetic"
    2018
    "arXiv:1807.05641v1"
    "arxiv:1807.05641"
    consistencyMetatheory
    stableArchiveIdentifier

------------------------------------------------------------------------
-- Provenance boundary.
------------------------------------------------------------------------

record FormalizationRecoverySourceBoundary : Set where
  constructor formalizationRecoverySourceBoundary
  field
    sourcesAreCalibrationNotProofCertificates : Bool
    sourcesAreCalibrationNotProofCertificatesIsTrue :
      sourcesAreCalibrationNotProofCertificates ≡ true

    provisionalJournalDOIPromotedWithoutVerification : Bool
    provisionalJournalDOIPromotedWithoutVerificationIsFalse :
      provisionalJournalDOIPromotedWithoutVerification ≡ false

    repositoryPermanentIdentifierDistinguishedFromArticleDOI : Bool
    repositoryPermanentIdentifierDistinguishedFromArticleDOIIsTrue :
      repositoryPermanentIdentifierDistinguishedFromArticleDOI ≡ true

canonicalFormalizationRecoverySourceBoundary :
  FormalizationRecoverySourceBoundary
canonicalFormalizationRecoverySourceBoundary =
  formalizationRecoverySourceBoundary
    true refl
    false refl
    true refl
