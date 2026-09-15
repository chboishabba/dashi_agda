module DASHI.Interop.ReadingTrailPNFProgressiveDisclosureExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Core.ReopenableProjectionComposition as Reopenable

------------------------------------------------------------------------
-- READING TRAIL / PNF PROGRESSIVE DISCLOSURE
--
-- UI law:
--
--   literal text
--     -> optional role / meaning overlay
--     -> source inspection
--     -> bounded proof cone
--     -> wider context
--
-- is a family of query-indexed projections over one retained state.  Hiding
-- information at a shallow reading depth does not delete it, and exposing a
-- PNF/role annotation does not manufacture proposition truth, legal authority,
-- or user comprehension.
------------------------------------------------------------------------

data ReadingState : Set where
  maboState : ReadingState
  maboStateWithDifferentAuthorityAudit : ReadingState

data ReadableProjection : Set where
  sameReadableMaboExplanation : ReadableProjection

projectReadable : ReadingState → ReadableProjection
projectReadable maboState = sameReadableMaboExplanation
projectReadable maboStateWithDifferentAuthorityAudit = sameReadableMaboExplanation

data ReadingQuery : Set where
  layMeaningQuestion : ReadingQuery
  primaryAuthorityAuditQuestion : ReadingQuery

data LayMeaningAnswer : Set where
  maboChangedLegalArgumentSpace : LayMeaningAnswer

data AuthorityAuditAnswer : Set where
  authorityAuditPaid : AuthorityAuditAnswer
  authorityAuditResidual : AuthorityAuditAnswer

ReadingAnswer : ReadingQuery → Set
ReadingAnswer layMeaningQuestion = LayMeaningAnswer
ReadingAnswer primaryAuthorityAuditQuestion = AuthorityAuditAnswer

askReading : (query : ReadingQuery) → ReadingState → ReadingAnswer query
askReading layMeaningQuestion maboState = maboChangedLegalArgumentSpace
askReading layMeaningQuestion maboStateWithDifferentAuthorityAudit = maboChangedLegalArgumentSpace
askReading primaryAuthorityAuditQuestion maboState = authorityAuditPaid
askReading primaryAuthorityAuditQuestion maboStateWithDifferentAuthorityAudit = authorityAuditResidual

readingQuestions : Query.InquiryQuestionFamily ReadingState ReadingQuery
readingQuestions = Query.inquiryQuestionFamily ReadingAnswer askReading

layMeaningFactorsThroughReadable :
  Query.FactorsThrough readingQuestions projectReadable layMeaningQuestion
layMeaningFactorsThroughReadable = Query.factorsThrough answer proof
  where
    answer : ReadableProjection → LayMeaningAnswer
    answer sameReadableMaboExplanation = maboChangedLegalArgumentSpace

    proof :
      (state : ReadingState) →
      askReading layMeaningQuestion state ≡ answer (projectReadable state)
    proof maboState = refl
    proof maboStateWithDifferentAuthorityAudit = refl

authorityAuditDoesNotFactorThroughReadable :
  Query.FactorsThrough
    readingQuestions
    projectReadable
    primaryAuthorityAuditQuestion →
  ⊥
authorityAuditDoesNotFactorThroughReadable factor = impossible
  where
    open Query.FactorsThrough factor

    left : authorityAuditPaid ≡ quotientAnswer sameReadableMaboExplanation
    left = factorisation maboState

    right : authorityAuditResidual ≡ quotientAnswer sameReadableMaboExplanation
    right = factorisation maboStateWithDifferentAuthorityAudit

    impossible : ⊥
    impossible = helper left right
      where
        helper :
          authorityAuditPaid ≡ quotientAnswer sameReadableMaboExplanation →
          authorityAuditResidual ≡ quotientAnswer sameReadableMaboExplanation →
          ⊥
        helper refl ()

------------------------------------------------------------------------
-- Reopenability: the shallow display may omit distinctions while the retained
-- receipt can reconstruct the original state exactly.  No minimality claim is
-- made for this receipt.
------------------------------------------------------------------------

readableReopenable :
  Reopenable.ExactReopenableProjection ReadingState ReadableProjection
readableReopenable =
  Reopenable.exactReopenableProjection
    ReadingState
    projectReadable
    (λ state → state)
    (λ projection receipt → receipt)
    (λ state → refl)

------------------------------------------------------------------------
-- PNF / semantic-reading overlay.
------------------------------------------------------------------------

data TokenRole : Set where
  actorRole : TokenRole
  predicateRole : TokenRole
  patientRole : TokenRole
  modifierRole : TokenRole
  negationRole : TokenRole
  modalityRole : TokenRole
  conditionRole : TokenRole
  otherRole : TokenRole

record LiteralToken : Set where
  constructor literalToken
  field
    tokenId : Bool

record RoleOverlay : Set where
  constructor roleOverlay
  field
    literal : LiteralToken
    role : TokenRole
    anchoredToLiteral : Bool

canonicalToken : LiteralToken
canonicalToken = literalToken true

canonicalPredicateOverlay : RoleOverlay
canonicalPredicateOverlay = roleOverlay canonicalToken predicateRole true

overlayRetainsLiteral :
  RoleOverlay.literal canonicalPredicateOverlay ≡ canonicalToken
overlayRetainsLiteral = refl

------------------------------------------------------------------------
-- WrongType-style firewalls.
------------------------------------------------------------------------

data RoleOverlayCreatesTruthPermission : Set where

data RoleOverlayCreatesAuthorityPermission : Set where

data InteractionCreatesComprehensionPermission : Set where

data ContextLinkPaysEvidencePermission : Set where

roleOverlayCannotManufactureTruth :
  RoleOverlayCreatesTruthPermission → ⊥
roleOverlayCannotManufactureTruth ()

roleOverlayCannotManufactureAuthority :
  RoleOverlayCreatesAuthorityPermission → ⊥
roleOverlayCannotManufactureAuthority ()

interactionReceiptCannotManufactureComprehension :
  InteractionCreatesComprehensionPermission → ⊥
interactionReceiptCannotManufactureComprehension ()

contextLinkCannotPayEvidence :
  ContextLinkPaysEvidencePermission → ⊥
contextLinkCannotPayEvidence ()

------------------------------------------------------------------------
-- Progressive disclosure levels are views, not semantic promotions.
------------------------------------------------------------------------

data DisclosureDepth : Set where
  literalDepth : DisclosureDepth
  meaningDepth : DisclosureDepth
  sourceDepth : DisclosureDepth
  proofConeDepth : DisclosureDepth
  worldContextDepth : DisclosureDepth

record ProgressiveDisclosureBoundary : Set where
  constructor progressiveDisclosureBoundary
  field
    literalRemainsPrimary : Bool
    roleOverlayOptional : Bool
    sourceReopenable : Bool
    proofConeBoundedByDefault : Bool
    worldGraphRequiresExplicitBroadening : Bool
    viewDepthChangesSemanticState : Bool
    viewDepthCreatesAuthority : Bool

canonicalBoundary : ProgressiveDisclosureBoundary
canonicalBoundary =
  progressiveDisclosureBoundary true true true true true false false

viewDepthDoesNotChangeSemanticState :
  ProgressiveDisclosureBoundary.viewDepthChangesSemanticState canonicalBoundary ≡ false
viewDepthDoesNotChangeSemanticState = refl

viewDepthDoesNotCreateAuthority :
  ProgressiveDisclosureBoundary.viewDepthCreatesAuthority canonicalBoundary ≡ false
viewDepthDoesNotCreateAuthority = refl

------------------------------------------------------------------------
-- Reading-trail navigation receipts describe interaction, not cognition.
------------------------------------------------------------------------

data TrailAction : Set where
  activate : TrailAction
  meaning : TrailAction
  openSource : TrailAction
  follow : TrailAction
  expandReasoning : TrailAction
  back : TrailAction

record ReadingTrailReceipt : Set where
  constructor readingTrailReceipt
  field
    action : TrailAction
    semanticTargetPresent : Bool
    beliefInferred : Bool
    comprehensionInferred : Bool

canonicalFollowReceipt : ReadingTrailReceipt
canonicalFollowReceipt = readingTrailReceipt follow true false false

followDoesNotInferBelief :
  ReadingTrailReceipt.beliefInferred canonicalFollowReceipt ≡ false
followDoesNotInferBelief = refl

followDoesNotInferComprehension :
  ReadingTrailReceipt.comprehensionInferred canonicalFollowReceipt ≡ false
followDoesNotInferComprehension = refl
