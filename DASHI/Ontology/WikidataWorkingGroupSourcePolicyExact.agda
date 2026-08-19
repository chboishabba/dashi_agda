module DASHI.Ontology.WikidataWorkingGroupSourcePolicyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- WIKIDATA / JMD HANDOFF SOURCE POLICY
--
-- Public external-source dependencies should be represented by the repository's
-- `AttributedSource` carrier (or by an exact source-hash/theorem contract where
-- the dependency is executable source code).  DOI state is never represented by
-- an empty string: it is either a recorded DOI or an explicit atlas-local
-- no-DOI state.
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
    true true true
    (Source.citationImportsProof source)
    (Source.citationCreatesAuthority source)

-- The two final fields above are intentionally false in the source carrier.
-- Expose the proof-shaped boundary directly rather than counting a citation as
-- proof or institutional/edit authority.
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
