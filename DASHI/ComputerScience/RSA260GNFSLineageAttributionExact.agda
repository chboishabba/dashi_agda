module DASHI.ComputerScience.RSA260GNFSLineageAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as SnowballAttribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as ExternalIdentity
import DASHI.ComputerScience.RSA260SnowballPrimaryAttributionExact as RSA260

------------------------------------------------------------------------
-- RSA-260 GNFS / CADO-NFS LINEAGE ATTRIBUTION
--
-- Distinguish four relationships that are easy to collapse in prose:
--   1. algorithmic lineage: GNFS literature;
--   2. software implementation provenance: CADO-NFS;
--   3. implementation derivation: Lu/Devin modifications of CADO-NFS;
--   4. execution/result: the RSA-260 run and resulting factorization.
--
-- Citation or software ancestry does not itself prove semantic equivalence,
-- correctness of the modified implementation, or reproduction of the run.
------------------------------------------------------------------------

gnfsFoundationalSource : Attribution.AttributedSource
gnfsFoundationalSource =
  Attribution.mkDOISource
    "A. K. Lenstra; H. W. Lenstra Jr.; M. S. Manasse; J. M. Pollard"
    "The Number Field Sieve"
    "Proceedings of the 22nd Annual ACM Symposium on Theory of Computing"
    "1990"
    "10.1145/100216.100295"
    "https://doi.org/10.1145/100216.100295"
    Attribution.academicArticleSource
    "historical algorithmic-lineage source for the number field sieve; does not identify the later CADO-NFS codebase, RSA-260 implementation, or execution"
    Attribution.publicAttribution

cadoNfsProjectSource : Attribution.AttributedSource
cadoNfsProjectSource =
  Attribution.mkNoDOISource
    "The CADO-NFS Development Team"
    "CADO-NFS, An Implementation of the Number Field Sieve Algorithm"
    "CADO-NFS project / INRIA"
    "development version"
    "https://cado-nfs.gitlabpages.inria.fr/"
    (Attribution.namedSourceKind "open-source scientific software project")
    "primary software-provenance carrier for the complete C/C++ NFS implementation, pipeline stages, project authorship guidance, licensing, and development repository identity"
    Attribution.publicAttribution

rsa260LineageSourceAtlas : Attribution.AttributedSourceAtlas
rsa260LineageSourceAtlas =
  Attribution.mkSourceAtlas
    "RSA-260 GNFS and CADO-NFS lineage"
    "DASHI.ComputerScience.RSA260GNFSLineageAttributionExact"
    (gnfsFoundationalSource ∷ cadoNfsProjectSource ∷ RSA260.rsa260CognitionTechnicalSource ∷ [])
    "retains algorithm literature, software project provenance, and RSA-260 implementation/run attribution as separate source roles"

gnfsSnowball : SnowballAttribution.SourceRoleSnowballReceipt gnfsFoundationalSource
gnfsSnowball = SnowballAttribution.canonicalSourceRoleSnowballReceipt gnfsFoundationalSource

cadoSnowball : SnowballAttribution.SourceRoleSnowballReceipt cadoNfsProjectSource
cadoSnowball = SnowballAttribution.canonicalSourceRoleSnowballReceipt cadoNfsProjectSource

------------------------------------------------------------------------
-- External identities.
------------------------------------------------------------------------

gnfsDOIDemand : ExternalIdentity.ExternalIdentityDemand
gnfsDOIDemand =
  ExternalIdentity.mkOptionalIdentityDemand
    "GNFS algorithm lineage"
    "Lenstra Lenstra Manasse Pollard The Number Field Sieve 1990"
    "The Number Field Sieve"
    ExternalIdentity.doi
    (ExternalIdentity.verified
      "ACM DOI"
      "10.1145/100216.100295")

cadoCanonicalURLDemand : ExternalIdentity.ExternalIdentityDemand
cadoCanonicalURLDemand =
  ExternalIdentity.mkOptionalIdentityDemand
    "CADO-NFS software provenance"
    "CADO-NFS Development Team official project"
    "CADO-NFS"
    ExternalIdentity.canonicalURL
    (ExternalIdentity.verified
      "official CADO-NFS project site"
      "https://cado-nfs.gitlabpages.inria.fr/")

cadoHALIdentifierDemand : ExternalIdentity.ExternalIdentityDemand
cadoHALIdentifierDemand =
  ExternalIdentity.mkOptionalIdentityDemand
    "CADO-NFS software provenance"
    "CADO-NFS HAL software record"
    "CADO-NFS"
    ExternalIdentity.officialIdentifier
    (ExternalIdentity.candidate
      "INRIA bibliography records a HAL software entry"
      "hal-02099620")

------------------------------------------------------------------------
-- Relationship-indexed lineage.
------------------------------------------------------------------------

data LineageRelationship : Set where
  algorithmicLineage : LineageRelationship
  softwareImplementsAlgorithm : LineageRelationship
  implementationDerivedFromSoftware : LineageRelationship
  implementationExecutedOnTarget : LineageRelationship
  executionProducedFactorization : LineageRelationship

record LineageEdge : Set where
  constructor lineage-edge
  field
    subjectReference : String
    relationship : LineageRelationship
    objectReference : String
    sourceReference : String
    sourceRole : String
    sameObjectIdentityPaid : Bool
    independentReproductionPaid : Bool
    edgeCreatesAlgorithmAuthorship : Bool
    edgeCreatesSoftwareAuthorship : Bool
open LineageEdge public

gnfsToCado : LineageEdge
gnfsToCado =
  lineage-edge
    "general number field sieve"
    softwareImplementsAlgorithm
    "CADO-NFS"
    "official CADO-NFS project site"
    "project documentation states CADO-NFS is a complete implementation of NFS"
    true false false false

cadoToLuDevinImplementation : LineageEdge
cadoToLuDevinImplementation =
  lineage-edge
    "CADO-NFS upstream implementation"
    implementationDerivedFromSoftware
    "Lu/Devin RSA-260 GPU-modified implementation"
    "Eric Lu, Factoring RSA-260, Cognition, 2026-09-09"
    "first-party technical account states the implementation was a significantly modified CADO-NFS and describes modified/untouched components"
    true false false false

luDevinImplementationToRun : LineageEdge
luDevinImplementationToRun =
  lineage-edge
    "Lu/Devin RSA-260 GPU-modified implementation"
    implementationExecutedOnTarget
    "RSA-260 factorization run"
    "Eric Lu, Factoring RSA-260, Cognition, 2026-09-09"
    "first-party run chronology and implementation account"
    true false false false

runToFactors : LineageEdge
runToFactors =
  lineage-edge
    "RSA-260 factorization run"
    executionProducedFactorization
    "published RSA-260 factors"
    "Eric Lu, Factoring RSA-260, Cognition, 2026-09-09"
    "first-party factor output and production timestamp; arithmetic identity separately externally checked"
    true false false false

------------------------------------------------------------------------
-- Attribution / WrongType firewalls.
------------------------------------------------------------------------

data AlgorithmPaperAuthorsOwnCadoCode : Set where
data CadoAuthorsOwnLuDevinModifications : Set where
data LuNamedOnResultMeansSoleAlgorithmAuthor : Set where
data DevinImplementationMeansGNFSWasAIOriginated : Set where
data SoftwareDerivationImpliesSemanticEquivalence : Set where
data FirstPartyRunAccountImpliesIndependentReproduction : Set where
data OpenSourceProjectImpliesSpecificRevisionUsed : Set where

algorithmAuthorsDoNotBecomeSoftwareAuthors : AlgorithmPaperAuthorsOwnCadoCode → ⊥
algorithmAuthorsDoNotBecomeSoftwareAuthors ()

upstreamAuthorsDoNotOwnDownstreamModifications : CadoAuthorsOwnLuDevinModifications → ⊥
upstreamAuthorsDoNotOwnDownstreamModifications ()

resultNamingDoesNotCreateSoleAlgorithmAuthorship : LuNamedOnResultMeansSoleAlgorithmAuthor → ⊥
resultNamingDoesNotCreateSoleAlgorithmAuthorship ()

aiImplementationDoesNotCreateGNFSOrigin : DevinImplementationMeansGNFSWasAIOriginated → ⊥
aiImplementationDoesNotCreateGNFSOrigin ()

derivationDoesNotProveSemanticEquivalence : SoftwareDerivationImpliesSemanticEquivalence → ⊥
derivationDoesNotProveSemanticEquivalence ()

firstPartyRunDoesNotCreateIndependentReproduction : FirstPartyRunAccountImpliesIndependentReproduction → ⊥
firstPartyRunDoesNotCreateIndependentReproduction ()

projectIdentityDoesNotPinExecutedRevision : OpenSourceProjectImpliesSpecificRevisionUsed → ⊥
projectIdentityDoesNotPinExecutedRevision ()

------------------------------------------------------------------------
-- Current residuals.
------------------------------------------------------------------------

record RSA260GNFSLineageBoundary : Set where
  constructor rsa260-gnfs-lineage-boundary
  field
    gnfsHistoricalDOIRetained : Bool
    cadoPrimaryProjectRetained : Bool
    cadoToModifiedImplementationRelationshipRetained : Bool
    modifiedImplementationToRunRelationshipRetained : Bool
    runToFactorRelationshipRetained : Bool
    exactUpstreamCadoRevisionUsedKnown : Bool
    publicModifiedSourceRevisionKnown : Bool
    independentExecutionReproductionPaid : Bool
    semanticEquivalenceToUpstreamCadoPaid : Bool
    lineageCreatesAlgorithmAuthorship : Bool
open RSA260GNFSLineageBoundary public

canonicalRSA260GNFSLineageBoundary : RSA260GNFSLineageBoundary
canonicalRSA260GNFSLineageBoundary =
  rsa260-gnfs-lineage-boundary
    true true true true true
    false false false false false
