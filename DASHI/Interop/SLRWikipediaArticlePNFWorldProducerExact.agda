module DASHI.Interop.SLRWikipediaArticlePNFWorldProducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as SpacyPNF
import DASHI.Interop.SLRSemanticWorldClosureExact as Closure
import DASHI.Interop.SLRWikidataTypedTraversalParetoExact as Route
import DASHI.Wikimedia.SensibLawNatClimateSLRFixtureExact as Nat

------------------------------------------------------------------------
-- REVISION-PINNED ARTICLE TEXT -> SPACY DEPENDENCIES -> CANDIDATE PNF -> WORLD
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_wikipedia_article_pnf_world_producer.py
--
-- This owner makes the parser/PNF seam explicit in the world-research loop.
-- Article text is a source manifestation.  spaCy dependency observations are
-- structural evidence.  They propose candidate semantic fragments/PNF but do
-- not become ontology truth or claim truth.  QID identity of the article pays
-- only the surface identity coordinate; span/entity and claim/property welds
-- remain separate obligations.
------------------------------------------------------------------------

record ArticleRevisionManifestation : Set where
  constructor articleRevisionManifestation
  field
    qidReference : String
    languageReference : String
    titleReference : String
    pageIdReference : String
    revisionIdReference : String
    revisionTimestampReference : String
    revisionSha1Reference : String
    sourceTextSha256Reference : String
    characterCountReference : String
    revisionPinned : Bool
    articleTextCreatesClaimTruth : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open ArticleRevisionManifestation public

record SpacyPNFProducerBoundary : Set where
  constructor spacyPNFProducerBoundary
  field
    sourceManifestationPrecedesParser : Bool
    trainedDependencyParserRequired : Bool
    spacyDependencySurfaceExplicit : Bool
    pnfCandidateSurfaceExplicit : Bool
    discourseAndRoleFibresRemainCandidate : Bool
    parserOutputCreatesOntologyTruth : Bool
    parserOutputCreatesClaimTruth : Bool
    surfaceQidIdentityPaysSpanEntityIdentity : Bool
    surfaceQidIdentityPaysClaimPropertyWeld : Bool
    qidPropertyWeldMaySkipSameObjectIdentity : Bool
    articleManifestationMayRewriteOtherLanguageSource : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open SpacyPNFProducerBoundary public

canonicalSpacyPNFProducerBoundary : SpacyPNFProducerBoundary
canonicalSpacyPNFProducerBoundary =
  spacyPNFProducerBoundary
    true true true true true
    false false false false false false
    true false

record CandidatePNFWorldWeld : Set where
  constructor candidatePNFWorldWeld
  field
    documentReference : String
    claimCandidateReference : String
    surfaceQidReference : String
    sourceSpanReference : String
    dependencyReceiptReference : String
    pnfProposalReference : String
    worldResidualReference : String
    surfaceQidIdentityPaid : Bool
    spanEntityIdentityPaid : Bool
    qidPropertyWeldPaid : Bool
    claimSemanticEquivalencePaid : Bool
    claimTruthPromoted : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open CandidatePNFWorldWeld public

canonicalCandidatePNFWorldWeld : CandidatePNFWorldWeld
canonicalCandidatePNFWorldWeld =
  candidatePNFWorldWeld
    "wiki:<QID>:<language>:<revision>"
    "pnf-candidate:<sha256>"
    "surface-qid"
    "source-span:start:end"
    "spacy-trained-dependency-receipt"
    "candidate-logical-pnf"
    "consumer-relative-world-residual"
    true false false false false true false

record GenericTextWorldProducerABI : Set where
  constructor genericTextWorldProducerABI
  field
    wikipediaArticleUsesABI : Bool
    sensibLawSourceUnitUsesABI : Bool
    natClimateFixtureUsesABI : Bool
    sourceHashRequired : Bool
    revisionOrSnapshotReferenceRequired : Bool
    parserExecutorRecorded : Bool
    pnfProposalContractRecorded : Bool
    sourceRoleRetained : Bool
    conflictFibresRetained : Bool
    promotionRequiresSeparateReceipt : Bool

open GenericTextWorldProducerABI public

canonicalGenericTextWorldProducerABI : GenericTextWorldProducerABI
canonicalGenericTextWorldProducerABI =
  genericTextWorldProducerABI
    true true true true true true true true true true

-- Existing formal seams are intentionally imported, not reconstructed here.
spacyCandidateFibreAnchor : Set
spacyCandidateFibreAnchor = SpacyPNF.CandidateSemanticFibre

semanticClosureAnchor : Closure.SemanticClosureBoundary
semanticClosureAnchor = Closure.canonicalSemanticClosureBoundary

typedRouteAnchor : Route.TypedTraversalBoundary
typedRouteAnchor = Route.canonicalTypedTraversalBoundary

natSourceUnitAnchor : String
natSourceUnitAnchor = "unit:wikidata_user_sandbox:nat_wdu:p5991_p14143:2026-04-01"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ParserOutputIsOntologyTruth : Set where
data ParserCandidateIsClaimTruth : Set where
data ArticleQidPaysSpanEntityIdentity : Set where
data ArticleQidPaysPropertyWeld : Set where
data ArticleTextMayRewriteOtherLanguageManifestation : Set where
data NatParsedSourceUnitMeansMigrationApproved : Set where
data CandidatePNFMaySkipConsumerResidual : Set where

parserOutputDoesNotCreateOntologyTruth : ParserOutputIsOntologyTruth → ⊥
parserOutputDoesNotCreateOntologyTruth ()

parserCandidateDoesNotCreateClaimTruth : ParserCandidateIsClaimTruth → ⊥
parserCandidateDoesNotCreateClaimTruth ()

articleQidDoesNotPaySpanEntityIdentity : ArticleQidPaysSpanEntityIdentity → ⊥
articleQidDoesNotPaySpanEntityIdentity ()

articleQidDoesNotPayPropertyWeld : ArticleQidPaysPropertyWeld → ⊥
articleQidDoesNotPayPropertyWeld ()

articleTextDoesNotRewriteOtherLanguage : ArticleTextMayRewriteOtherLanguageManifestation → ⊥
articleTextDoesNotRewriteOtherLanguageManifestation ()

natParsingDoesNotApproveMigration : NatParsedSourceUnitMeansMigrationApproved → ⊥
natParsingDoesNotApproveMigration ()

candidatePNFStillRequiresConsumerResidual : CandidatePNFMaySkipConsumerResidual → ⊥
candidatePNFStillRequiresConsumerResidual ()
