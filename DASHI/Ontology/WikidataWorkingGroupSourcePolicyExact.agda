module DASHI.Ontology.WikidataWorkingGroupSourcePolicyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- WIKIDATA / JMD HANDOFF SOURCE POLICY
------------------------------------------------------------------------

data ExternalSourceRegistration : Set where
  attributedBibliographicSource : Source.AttributedSource → ExternalSourceRegistration
  sourcePinnedFormalContract :
    String →  -- source / archive identity
    String →  -- content hash / revision
    String →  -- theorem or contract name
    ExternalSourceRegistration

record PublicSourceRequirement : Set₁ where
  constructor publicSourceRequirement
  field
    registration : ExternalSourceRegistration
    authorTitlePublicationRetainedWhenBibliographic : Bool
    doiStateExplicitWhenBibliographic : Bool
    sourceRelationshipExplicit : Bool
    provenanceDoesNotSelfPromoteToProof : Bool
    provenanceDoesNotSelfPromoteToAuthority : Bool

open PublicSourceRequirement public

requireAttributedSource :
  (source : Source.AttributedSource) → PublicSourceRequirement
requireAttributedSource source =
  publicSourceRequirement
    (attributedBibliographicSource source)
    true true true true true

requirePinnedFormalSource :
  String → String → String → PublicSourceRequirement
requirePinnedFormalSource sourceIdentity revisionOrHash contractName =
  publicSourceRequirement
    (sourcePinnedFormalContract sourceIdentity revisionOrHash contractName)
    true true true true true

attributedSourceCannotImportProof :
  (source : Source.AttributedSource) →
  Source.citationImportsProof source ≡ false
attributedSourceCannotImportProof = Source.citationImportsProofIsFalse

attributedSourceCannotCreateAuthority :
  (source : Source.AttributedSource) →
  Source.citationCreatesAuthority source ≡ false
attributedSourceCannotCreateAuthority = Source.citationCreatesAuthorityIsFalse

record DOIRegistrationBoundary : Set where
  constructor doiRegistrationBoundary
  field
    doiMustBeRecordedOrExplicitlyAbsentInAtlas : Bool
    emptyStringUsedAsNoDOISentinel : Bool
    noDOIClaimIsGlobalClaimAboutPublicationHistory : Bool

canonicalDOIRegistrationBoundary : DOIRegistrationBoundary
canonicalDOIRegistrationBoundary =
  doiRegistrationBoundary true false false

record WorkingGroupSourcePolicyBoundary : Set where
  constructor workingGroupSourcePolicyBoundary
  field
    bareExternalLinkIsSufficientSourceRecord : Bool
    bibliographicSourcesRetainAuthorTitlePublicationAndDOIState : Bool
    executableFormalSourcesRetainRevisionHashAndContract : Bool
    sourceCountIsTruthWeight : Bool
    sourceMetadataCreatesEditAuthority : Bool

canonicalWorkingGroupSourcePolicyBoundary : WorkingGroupSourcePolicyBoundary
canonicalWorkingGroupSourcePolicyBoundary =
  workingGroupSourcePolicyBoundary false true true false false
