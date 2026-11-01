module DASHI.Interop.SLRSemanticWorldClosureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRMultilingualWikimediaParserCompatibilityExact as Multi
import DASHI.Interop.SLRWikimediaFirstWorldAcquisitionExact as Wikimedia

------------------------------------------------------------------------
-- SLR SEMANTIC WORLD CLOSURE
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_semantic_world_closure.py
--   tools/slr-discourse-reconstruct/run_semantic_world_closure.sh
--
-- Canonical closure admits only language-independent atoms whose identity is
-- paid independently of lexical translation: QIDs, Q/P edges and paid QID
-- related/world edges.  A propagated atom becomes available to a consumer of
-- another language surface, but it never rewrites what that surface said.
------------------------------------------------------------------------

data SemanticAtomKind : Set where
  qidIdentityAtom : SemanticAtomKind
  wikidataPropertyAtom : SemanticAtomKind
  wikipediaRelatedQidAtom : SemanticAtomKind
  paidWorldEdgeAtom : SemanticAtomKind
  surfaceLocalResidualAtom : SemanticAtomKind

record SurfaceObservation : Set where
  constructor surfaceObservation
  field
    rootQidReference : String
    languageReference : String
    surfaceReference : String
    atomReference : String
    atomKind : SemanticAtomKind
    atomIdentityPaid : Bool
    targetSurfaceAssertion : Bool
    claimTruthPromoted : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open SurfaceObservation public

record PropagatedEvidenceView : Set where
  constructor propagatedEvidenceView
  field
    atomReference : String
    sourceSurfaceReference : String
    targetSurfaceReference : String
    availableToTargetConsumer : Bool
    targetSurfaceAsserted : Bool
    translationEquivalencePaid : Bool
    claimSemanticEquivalencePaid : Bool
    appendOnly : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open PropagatedEvidenceView public

record SemanticGap : Set where
  constructor semanticGap
  field
    qidReference : String
    languageReference : String
    closureReference : String
    observedReference : String
    missingAtomReference : String
    acquisitionObligationReference : String
    gapCreatesClaimTruth : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open SemanticGap public

record SemanticClosureBoundary : Set where
  constructor semanticClosureBoundary
  field
    canonicalAtomsRequireLanguageIndependentIdentity : Bool
    propagatedEvidenceAvailableToTargetConsumer : Bool
    propagationRewritesTargetSurface : Bool
    articleLinkCreatesClaimTruth : Bool
    sameQidCreatesSemanticEquivalence : Bool
    simpleWikiPresumedSubsetOfEnglishWikipedia : Bool
    unresolvedLexicalPnfMayPropagateWithoutWeld : Bool
    contradictoryAtomsCollapsedAutomatically : Bool
    appendOnly : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open SemanticClosureBoundary public

canonicalSemanticClosureBoundary : SemanticClosureBoundary
canonicalSemanticClosureBoundary =
  semanticClosureBoundary true true false false false false false false true true false

multilingualBoundaryAnchor : Multi.MultilingualIdentityBoundary
multilingualBoundaryAnchor = Multi.canonicalMultilingualIdentityBoundary

wikimediaAcquisitionAnchor : Wikimedia.WikimediaFirstAcquisitionPolicy
wikimediaAcquisitionAnchor = Wikimedia.canonicalWikimediaFirstAcquisitionPolicy

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PropagationRewritesSource : Set where
data SharedQidCreatesSemanticEquivalence : Set where
data ArticleLinkCreatesClaimTruth : Set where
data SimpleWikiIsNecessarilyEnglishSubset : Set where
data UnweldedPnfMayBecomeSharedFact : Set where

propagationDoesNotRewriteSource : PropagationRewritesSource → ⊥
propagationDoesNotRewriteSource ()

sharedQidDoesNotCreateSemanticEquivalence : SharedQidCreatesSemanticEquivalence → ⊥
sharedQidDoesNotCreateSemanticEquivalence ()

articleLinkDoesNotCreateClaimTruth : ArticleLinkCreatesClaimTruth → ⊥
articleLinkDoesNotCreateClaimTruth ()

simpleWikiIsNotPresumedEnglishSubset : SimpleWikiIsNecessarilyEnglishSubset → ⊥
simpleWikiIsNotPresumedEnglishSubset ()

unweldedPnfDoesNotBecomeSharedFact : UnweldedPnfMayBecomeSharedFact → ⊥
unweldedPnfDoesNotBecomeSharedFact ()
