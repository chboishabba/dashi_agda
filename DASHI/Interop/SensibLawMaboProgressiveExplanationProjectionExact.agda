module DASHI.Interop.SensibLawMaboProgressiveExplanationProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- MABO / SENSIBLAW PROGRESSIVE EXPLANATION PROJECTION
--
-- Ownership boundary:
--   SensibLaw owns legal proposition identity, authority/application,
--   support/defeater/comparator roles, review/payment and legal explanation.
--   SLR owns the generic parse -> residual -> acquire -> parse recurrence.
--   JCUI / ITIR-Svelte owns user-facing projections over the same specimen.
--   StatiBaker may retain opted-in interaction observations only.
--
-- This module formalises UI/projection firewalls only.  It does not prove a
-- legal conclusion in Mabo and does not turn discovery/context sources into
-- legal authority.
------------------------------------------------------------------------

data ViewDepth : Set where
  explainView whyView sourceView contextView graphView guideView : ViewDepth

data ReadingCardKind : Set where
  identityCard sourceCard proofCard : ReadingCardKind

data ReadingPnfCue : Set where
  actorCue
  predicateCue
  patientCue
  negationCue
  modalityCue
  conditionCue
  temporalCue
  coreferenceCue : ReadingPnfCue

data BoundedReadingRole : Set where
  challengedPremiseRole
  historicalInputRole
  authorityPropositionRole
  immediateImplicationRole
  downstreamApplicationRole : BoundedReadingRole

data LegalTermLayer : Set where
  lexicalLayer encyclopediaLayer australianLawLayer contingentArgumentLayer : LegalTermLayer

data ChainStage : Set where
  literalArgumentStage
  authorityCandidateStage
  applicabilityStage
  supportStage
  defeaterStage
  comparatorStage
  residualStage
  explanationStage : ChainStage

------------------------------------------------------------------------
-- Exact runtime parity for src/pnf/mabo_proof_specimen.py.
--
-- These constructors mirror the Python enums without making this UI owner a
-- parser or a second legal semantics engine.  The Reading Lens merely asks a
-- question of the already-existing PNF carrier.
------------------------------------------------------------------------

data RuntimeReadingDepth : Set where
  readDepth inspectDepth traceDepth proveDepth : RuntimeReadingDepth

data RuntimeLegalChangeKind : Set where
  rejectedChange
  qualifiedChange
  distinguishedChange
  overruledChange
  displacedChange
  reinterpretedChange
  leftOpenChange : RuntimeLegalChangeKind

data RuntimeProofRole : Set where
  supportRole defeaterRole comparatorRole residualRole : RuntimeProofRole

data RuntimeReadingQuestion : Set where
  whoDidIt
  whatHappened
  toWhat
  howCertain
  assertedOrQuoted
  whenQuestion
  whoDoesThisReferTo : RuntimeReadingQuestion

data RuntimeTranslationLoss : Set where
  aspectLoss evidentialityLoss modalityLoss otherLoss : RuntimeTranslationLoss

readingQuestionCue : RuntimeReadingQuestion → ReadingPnfCue
readingQuestionCue whoDidIt = actorCue
readingQuestionCue whatHappened = predicateCue
readingQuestionCue toWhat = patientCue
readingQuestionCue howCertain = modalityCue
readingQuestionCue assertedOrQuoted = conditionCue
readingQuestionCue whenQuestion = temporalCue
readingQuestionCue whoDoesThisReferTo = coreferenceCue

maboWikidataQid : String
maboWikidataQid = "Q1501525"

record RuntimeReadingConeParity : Set where
  constructor runtimeReadingConeParity
  field
    canonicalSpecimenHasFiveBoundedNodes : Bool
    literalFormulationSeparateFromInferredIssue : Bool
    readViewHidesInternalIds : Bool
    readViewHidesProofGraph : Bool
    everyVisibleNodeRetainsSourceReopenRef : Bool
    everyVisibleNodeRetainsProofReopenRef : Bool
    hiddenInformationDiscarded : Bool
    readingLensCreatesNewGrammarSemantics : Bool
    readingLensRoleProjectionClaimsTruth : Bool
    flagshipChangeKindIsRejected : Bool
    worldTruthClaimed : Bool
    legalConclusionClaimed : Bool
    wikidataIdentityIsLegalAuthority : Bool
    wikipediaIsPrimaryAuthority : Bool
    fullPrimarySourceRequiredForPayment : Bool

open RuntimeReadingConeParity public

canonicalRuntimeReadingConeParity : RuntimeReadingConeParity
canonicalRuntimeReadingConeParity =
  runtimeReadingConeParity
    true
    true
    true
    true
    true
    true
    false
    false
    false
    true
    false
    false
    false
    false
    true

record MultilingualReadingSurfaceBoundary : Set where
  constructor multilingualReadingSurfaceBoundary
  field
    qidIdentityMayBePaid : Bool
    semanticEquivalencePaidBySameQid : Bool
    roleCarrierCompatibilityMayBeObserved : Bool
    roleCarrierCompatibilityPaysExactTranslation : Bool
    translationLossesRemainExplicit : Bool
    aspectLossRepresentable : Bool
    evidentialityLossRepresentable : Bool
    modalityLossRepresentable : Bool

open MultilingualReadingSurfaceBoundary public

canonicalMultilingualReadingSurfaceBoundary : MultilingualReadingSurfaceBoundary
canonicalMultilingualReadingSurfaceBoundary =
  multilingualReadingSurfaceBoundary
    true
    false
    true
    false
    true
    true
    true
    true

record ExplanationAnchorBoundary : Set where
  constructor explanationAnchorBoundary
  field
    explanationClaimHasProofRef : Bool
    explanationClaimHasSourceRef : Bool
    exactSourceViewHasSpanRef : Bool
    exactSourceViewHasRevisionRef : Bool
    navigationChangesSemanticState : Bool
    hiddenMeansDiscarded : Bool
    hiddenMeansUnavailable : Bool
    hiddenMeansUnsupported : Bool

open ExplanationAnchorBoundary public

canonicalExplanationAnchorBoundary : ExplanationAnchorBoundary
canonicalExplanationAnchorBoundary =
  explanationAnchorBoundary
    true
    true
    true
    true
    false
    false
    false
    false

------------------------------------------------------------------------
-- JCUI runtime parity.
--
-- JesusCrust's ReadingSurface is a projection over one Semantic target.  It
-- may open a separate Source target, but switching Explain/Why/Source/
-- Context/Graph/Guide never changes the underlying semantic identity.
------------------------------------------------------------------------

record JCUIReadingSurfaceParity : Set where
  constructor jcuiReadingSurfaceParity
  field
    siblingViewsPreserveSemanticRef : Bool
    sourceCardUsesDistinctSourceRef : Bool
    whyUsesSemanticExpand : Bool
    contextUsesSemanticFollow : Bool
    graphUsesSemanticZoomFit : Bool
    guideUsesSameSemanticRef : Bool
    guideExposesActorPredicatePatient : Bool
    guideInteractionCreatesUnderstanding : Bool
    identitySourceProofCardsCollapsed : Bool
    boundedDefaultHasFiveRoles : Bool
    graphVisibleByDefault : Bool
    contextVisibleByDefault : Bool
    guideVisibleByDefault : Bool

open JCUIReadingSurfaceParity public

canonicalJCUIReadingSurfaceParity : JCUIReadingSurfaceParity
canonicalJCUIReadingSurfaceParity =
  jcuiReadingSurfaceParity
    true
    true
    true
    true
    true
    true
    true
    false
    false
    true
    false
    false
    false

record MaboThinProfileBoundary : Set where
  constructor maboThinProfileBoundary
  field
    sensibLawOwnsLegalMeaning : Bool
    slrOwnsResidualAcquisitionRecurrence : Bool
    uiOwnsProjectionOnly : Bool
    slrRouteSelectionCreatesLegalConclusion : Bool
    acquiredAuthorityCandidateIsApplicableAuthority : Bool
    acquiredSourceCreatesEvidencePayment : Bool
    sourceAgreementCreatesIndependentAncestry : Bool
    supportDefeaterComparatorCollapsed : Bool
    exactCommonGroundGeneratesFurtherAcquisition : Bool

open MaboThinProfileBoundary public

canonicalMaboThinProfileBoundary : MaboThinProfileBoundary
canonicalMaboThinProfileBoundary =
  maboThinProfileBoundary
    true
    true
    true
    false
    false
    false
    false
    false
    false

record PrimaryAuthorityPaymentBoundary : Set where
  constructor primaryAuthorityPaymentBoundary
  field
    searchSnippetMayPayPrimaryAuthority : Bool
    encyclopediaLeadMayPayPrimaryAuthority : Bool
    fullVerifiedSourceRequired : Bool
    exactSourceSpanRequired : Bool
    admittedSourceRoleRequired : Bool
    reviewPaymentDecisionRequired : Bool

open PrimaryAuthorityPaymentBoundary public

canonicalPrimaryAuthorityPaymentBoundary : PrimaryAuthorityPaymentBoundary
canonicalPrimaryAuthorityPaymentBoundary =
  primaryAuthorityPaymentBoundary false false true true true true

record ContextNavigationBoundary : Set where
  constructor contextNavigationBoundary
  field
    wiktionaryMayProvideLexicalOrientation : Bool
    wikipediaMayProvideContextNavigation : Bool
    wikidataMayProvideEntityIdentityCandidate : Bool
    publicOntologyMayProvideCandidateIdentity : Bool
    lexicalDefinitionCreatesAustralianLegalRule : Bool
    wikipediaCreatesLegalAuthority : Bool
    qidIdentityCreatesApplicability : Bool
    contextLinkCreatesEvidencePayment : Bool
    australianLawLayerIsDemandDriven : Bool
    contingentArgumentsAreDemandDriven : Bool

open ContextNavigationBoundary public

canonicalContextNavigationBoundary : ContextNavigationBoundary
canonicalContextNavigationBoundary =
  contextNavigationBoundary
    true
    true
    true
    true
    false
    false
    false
    false
    true
    true

record PublicInterestExplanationBoundary : Set where
  constructor publicInterestExplanationBoundary
  field
    literalFormulationRetained : Bool
    inferredIssueRetainedSeparately : Bool
    predicateEventsMayBeExposed : Bool
    authorityCandidatesMayBeExposed : Bool
    contraryMaterialMayBeExposed : Bool
    unresolvedResidualsMayBeExposed : Bool
    typedArgumentCreatesStanding : Bool
    typedArgumentCreatesLegalAdvice : Bool
    typedArgumentCreatesClaimTruth : Bool

open PublicInterestExplanationBoundary public

canonicalPublicInterestExplanationBoundary : PublicInterestExplanationBoundary
canonicalPublicInterestExplanationBoundary =
  publicInterestExplanationBoundary
    true true true true true true false false false

------------------------------------------------------------------------
-- Query-indexed projection witness.
--
-- The same lay explanation surface can be adequate for a lay explanatory
-- query while being insufficient for primary-authority audit.  Therefore the
-- default explanation view must remain reopenable to richer source/proof
-- coordinates rather than pretending to be intrinsically adequate.
------------------------------------------------------------------------

data SpecimenState : Set where
  sourceVersionA sourceVersionB : SpecimenState

data ExplainObservation : Set where
  sameLayExplanation : ExplainObservation

data ProjectionQuery : Set where
  layExplanationQuery primaryAuthorityAuditQuery : ProjectionQuery

data ProjectionAnswer : Set where
  layExplanationAnswer sourceVersionAAnswer sourceVersionBAnswer : ProjectionAnswer

explainProjection : SpecimenState → ExplainObservation
explainProjection sourceVersionA = sameLayExplanation
explainProjection sourceVersionB = sameLayExplanation

projectionAnswer : ProjectionQuery → SpecimenState → ProjectionAnswer
projectionAnswer layExplanationQuery sourceVersionA = layExplanationAnswer
projectionAnswer layExplanationQuery sourceVersionB = layExplanationAnswer
projectionAnswer primaryAuthorityAuditQuery sourceVersionA = sourceVersionAAnswer
projectionAnswer primaryAuthorityAuditQuery sourceVersionB = sourceVersionBAnswer

projectionSemantics : Query.QuerySemantics SpecimenState ProjectionQuery ProjectionAnswer
projectionSemantics = Query.querySemantics projectionAnswer

layExplanationFactorsThroughExplainView :
  Query.AdequateFor explainProjection projectionSemantics layExplanationQuery
layExplanationFactorsThroughExplainView =
  Query.factorsForQuery
    (λ _ → layExplanationAnswer)
    (λ state → refl)

primaryAuthorityAuditDefect :
  Query.QueryAdequacyDefect
    explainProjection
    projectionSemantics
    primaryAuthorityAuditQuery
primaryAuthorityAuditDefect =
  Query.queryAdequacyDefect
    sourceVersionA
    sourceVersionB
    refl
    (λ ())

primaryAuthorityAuditDoesNotFactorThroughExplainView :
  Query.AdequateFor
    explainProjection
    projectionSemantics
    primaryAuthorityAuditQuery →
  ⊥
primaryAuthorityAuditDoesNotFactorThroughExplainView =
  Query.queryAdequacyDefectBlocksFactorisation primaryAuthorityAuditDefect

record ProgressiveDisclosureAdequacyReceipt : Set₁ where
  constructor progressiveDisclosureAdequacyReceipt
  field
    layExplanationAdequate :
      Query.AdequateFor explainProjection projectionSemantics layExplanationQuery
    primaryAuthorityNeedsRicherProjection :
      Query.QueryAdequacyDefect
        explainProjection
        projectionSemantics
        primaryAuthorityAuditQuery
    evidenceLossFromHiding : Bool
    richerViewMutatesProofState : Bool

canonicalProgressiveDisclosureAdequacyReceipt :
  ProgressiveDisclosureAdequacyReceipt
canonicalProgressiveDisclosureAdequacyReceipt =
  progressiveDisclosureAdequacyReceipt
    layExplanationFactorsThroughExplainView
    primaryAuthorityAuditDefect
    false
    false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ProgressiveDisclosureImpliesEvidenceLoss : Set where
data WikipediaCreatesLegalAuthority : Set where
data WiktionaryCreatesAustralianLegalRule : Set where
data QIDIdentityCreatesApplicability : Set where
data QIDIdentityCreatesSemanticEquivalence : Set where
data RoleCarrierCompatibilityCreatesExactTranslation : Set where
data ReadingLensRoleCreatesClaimTruth : Set where
data ContextNavigationPaysEvidence : Set where
data SLRRouteSelectionCreatesLegalConclusion : Set where
data AcquiredSourcePaysWithoutReview : Set where
data TypedPublicInterestArgumentCreatesStanding : Set where
data TypedPublicInterestArgumentCreatesLegalAdvice : Set where
data ReadingViewChangeMutatesSemanticIdentity : Set where
data GuideInteractionCreatesUnderstanding : Set where
data IdentitySourceProofCardsAreOneThing : Set where

progressiveDisclosureDoesNotLoseEvidence :
  ProgressiveDisclosureImpliesEvidenceLoss → ⊥
progressiveDisclosureDoesNotLoseEvidence ()

wikipediaIsNotLegalAuthority : WikipediaCreatesLegalAuthority → ⊥
wikipediaIsNotLegalAuthority ()

wiktionaryIsNotAustralianLegalRule : WiktionaryCreatesAustralianLegalRule → ⊥
wiktionaryIsNotAustralianLegalRule ()

qidIdentityIsNotApplicability : QIDIdentityCreatesApplicability → ⊥
qidIdentityIsNotApplicability ()

qidIdentityIsNotSemanticEquivalence : QIDIdentityCreatesSemanticEquivalence → ⊥
qidIdentityIsNotSemanticEquivalence ()

roleCarrierCompatibilityIsNotExactTranslation :
  RoleCarrierCompatibilityCreatesExactTranslation → ⊥
roleCarrierCompatibilityIsNotExactTranslation ()

readingLensRoleIsNotClaimTruth : ReadingLensRoleCreatesClaimTruth → ⊥
readingLensRoleIsNotClaimTruth ()

contextNavigationIsNotEvidencePayment : ContextNavigationPaysEvidence → ⊥
contextNavigationIsNotEvidencePayment ()

slrRouteSelectionIsNotLegalConclusion : SLRRouteSelectionCreatesLegalConclusion → ⊥
slrRouteSelectionIsNotLegalConclusion ()

acquiredSourceStillNeedsReview : AcquiredSourcePaysWithoutReview → ⊥
acquiredSourceStillNeedsReview ()

typedArgumentDoesNotCreateStanding : TypedPublicInterestArgumentCreatesStanding → ⊥
typedArgumentDoesNotCreateStanding ()

typedArgumentDoesNotCreateLegalAdvice : TypedPublicInterestArgumentCreatesLegalAdvice → ⊥
typedArgumentDoesNotCreateLegalAdvice ()

readingViewPreservesSemanticIdentity :
  ReadingViewChangeMutatesSemanticIdentity → ⊥
readingViewPreservesSemanticIdentity ()

guideInteractionIsNotUnderstanding : GuideInteractionCreatesUnderstanding → ⊥
guideInteractionIsNotUnderstanding ()

identitySourceAndProofRemainDistinct : IdentitySourceProofCardsAreOneThing → ⊥
identitySourceAndProofRemainDistinct ()
