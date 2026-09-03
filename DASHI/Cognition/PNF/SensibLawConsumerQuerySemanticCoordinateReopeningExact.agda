module DASHI.Cognition.PNF.SensibLawConsumerQuerySemanticCoordinateReopeningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact as Consumer
import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Core.RequiredAxisSupportSquareExact as Support

------------------------------------------------------------------------
-- CONSUMER + QUERY -> ACTIVE SEMANTIC COORDINATES
--
-- Cross-pollination:
--   * QueryIndexedProjectionAdequacyExact: adequacy is query-relative.
--   * ActiveObligationEvidenceFibreExact: inactive obligations are not failures.
--   * RequiredAxisSupportSquareExact: strength on one required axis cannot fill
--     a missing different axis.
--   * AffectedDependencyClosureExact: only dependency-affected products reopen.
--
-- SensibLaw therefore does NOT map a consumer label to one fixed pipeline.
-- The same consumer may ask a cheap structural/discourse question or a much
-- stronger governed question.  Multiple consumer/query requests contribute
-- simultaneous obligations over one unchanged semantic carrier.
------------------------------------------------------------------------

data SemanticQuery : Set where
  parseStructureQuery
  whoSaidWhatQuery
  provenanceHistoryQuery
  discourseContextQuery
  legalDiscourseRoleQuery
  legalApplicabilityQuery
  legalLiabilityQuery
  customQuery : String → SemanticQuery

data SemanticCoordinate : Set where
  syntaxCoordinate
  discourseCoordinate
  referenceCoordinate
  attributionCoordinate
  provenanceCoordinate
  temporalCoordinate
  scopeCoordinate
  propositionStatusCoordinate
  occurrenceCoordinate
  evidenceCoordinate
  documentContextCoordinate
  authorityCoordinate
  jurisdictionCoordinate
  legalRoleCoordinate
  applicabilityCoordinate
  violationCoordinate
  liabilityCoordinate
  : SemanticCoordinate

------------------------------------------------------------------------
-- Proof-bearing requirement relation.
--
-- General queries may be asked by ANY consumer.  Legal-specific coordinates
-- arise from the legal query being requested, not from legal-looking words or
-- merely selecting `legalConsumer`.
------------------------------------------------------------------------

data Requires :
    Consumer.ConsumerKind → SemanticQuery → SemanticCoordinate → Set where
  parseNeedsSyntax :
    ∀ {consumer} → Requires consumer parseStructureQuery syntaxCoordinate

  whoNeedsDiscourse :
    ∀ {consumer} → Requires consumer whoSaidWhatQuery discourseCoordinate
  whoNeedsReference :
    ∀ {consumer} → Requires consumer whoSaidWhatQuery referenceCoordinate
  whoNeedsAttribution :
    ∀ {consumer} → Requires consumer whoSaidWhatQuery attributionCoordinate

  historyNeedsDiscourse :
    ∀ {consumer} → Requires consumer provenanceHistoryQuery discourseCoordinate
  historyNeedsAttribution :
    ∀ {consumer} → Requires consumer provenanceHistoryQuery attributionCoordinate
  historyNeedsProvenance :
    ∀ {consumer} → Requires consumer provenanceHistoryQuery provenanceCoordinate
  historyNeedsTemporal :
    ∀ {consumer} → Requires consumer provenanceHistoryQuery temporalCoordinate

  contextNeedsDiscourse :
    ∀ {consumer} → Requires consumer discourseContextQuery discourseCoordinate
  contextNeedsDocumentContext :
    ∀ {consumer} → Requires consumer discourseContextQuery documentContextCoordinate

  legalRoleNeedsDiscourse :
    Requires Consumer.legalConsumer legalDiscourseRoleQuery discourseCoordinate
  legalRoleNeedsReference :
    Requires Consumer.legalConsumer legalDiscourseRoleQuery referenceCoordinate
  legalRoleNeedsAttribution :
    Requires Consumer.legalConsumer legalDiscourseRoleQuery attributionCoordinate
  legalRoleNeedsDocumentContext :
    Requires Consumer.legalConsumer legalDiscourseRoleQuery documentContextCoordinate

  legalApplicabilityNeedsProposition :
    Requires Consumer.legalConsumer legalApplicabilityQuery propositionStatusCoordinate
  legalApplicabilityNeedsOccurrence :
    Requires Consumer.legalConsumer legalApplicabilityQuery occurrenceCoordinate
  legalApplicabilityNeedsEvidence :
    Requires Consumer.legalConsumer legalApplicabilityQuery evidenceCoordinate
  legalApplicabilityNeedsContext :
    Requires Consumer.legalConsumer legalApplicabilityQuery documentContextCoordinate
  legalApplicabilityNeedsAuthority :
    Requires Consumer.legalConsumer legalApplicabilityQuery authorityCoordinate
  legalApplicabilityNeedsJurisdiction :
    Requires Consumer.legalConsumer legalApplicabilityQuery jurisdictionCoordinate
  legalApplicabilityNeedsScope :
    Requires Consumer.legalConsumer legalApplicabilityQuery scopeCoordinate

  legalLiabilityNeedsApplicability :
    Requires Consumer.legalConsumer legalLiabilityQuery applicabilityCoordinate
  legalLiabilityNeedsViolation :
    Requires Consumer.legalConsumer legalLiabilityQuery violationCoordinate
  legalLiabilityNeedsLegalRole :
    Requires Consumer.legalConsumer legalLiabilityQuery legalRoleCoordinate
  legalLiabilityNeedsEvidence :
    Requires Consumer.legalConsumer legalLiabilityQuery evidenceCoordinate
  legalLiabilityNeedsAuthority :
    Requires Consumer.legalConsumer legalLiabilityQuery authorityCoordinate
  legalLiabilityNeedsJurisdiction :
    Requires Consumer.legalConsumer legalLiabilityQuery jurisdictionCoordinate

record DemandRequest : Set where
  constructor demandRequest
  field
    consumer : Consumer.ConsumerKind
    query : SemanticQuery
    requestReference : String

open DemandRequest public

record RequirementWitness (request : DemandRequest) : Set where
  constructor requirementWitness
  field
    coordinate : SemanticCoordinate
    requirement : Requires (consumer request) (query request) coordinate
    requirementReference : String

open RequirementWitness public

record SemanticDemand : Set where
  constructor semanticDemand
  field
    requests : List DemandRequest
    requirements : List SemanticCoordinate
    requirementWitnessReferences : List String
    demandReference : String

open SemanticDemand public

------------------------------------------------------------------------
-- Canonical least-privilege requests.
------------------------------------------------------------------------

generalWhoSaidWhat : DemandRequest
generalWhoSaidWhat =
  demandRequest Consumer.generalSemanticConsumer whoSaidWhatQuery
    "general consumer asks who said what"

legalWhoSaidWhat : DemandRequest
legalWhoSaidWhat =
  demandRequest Consumer.legalConsumer whoSaidWhatQuery
    "legal consumer asks only who said what; legal applicability is not active"

legalSubmissionRole : DemandRequest
legalSubmissionRole =
  demandRequest Consumer.legalConsumer legalDiscourseRoleQuery
    "legal consumer asks whether the attributed discourse is a submission/finding/etc"

historicalProvenance : DemandRequest
historicalProvenance =
  demandRequest Consumer.historicalConsumer provenanceHistoryQuery
    "historical consumer asks provenance and temporal-source question"

legalApplicability : DemandRequest
legalApplicability =
  demandRequest Consumer.legalConsumer legalApplicabilityQuery
    "legal consumer asks governed applicability question"

legalLiability : DemandRequest
legalLiability =
  demandRequest Consumer.legalConsumer legalLiabilityQuery
    "legal consumer asks downstream liability question"

whoSaidWhatRequirements : List SemanticCoordinate
whoSaidWhatRequirements =
  discourseCoordinate ∷ referenceCoordinate ∷ attributionCoordinate ∷ []

legalDiscourseRoleRequirements : List SemanticCoordinate
legalDiscourseRoleRequirements =
  discourseCoordinate ∷ referenceCoordinate ∷ attributionCoordinate
  ∷ documentContextCoordinate ∷ []

historicalRequirements : List SemanticCoordinate
historicalRequirements =
  discourseCoordinate ∷ attributionCoordinate ∷ provenanceCoordinate
  ∷ temporalCoordinate ∷ []

legalApplicabilityRequirements : List SemanticCoordinate
legalApplicabilityRequirements =
  propositionStatusCoordinate ∷ occurrenceCoordinate ∷ evidenceCoordinate
  ∷ documentContextCoordinate ∷ authorityCoordinate ∷ jurisdictionCoordinate
  ∷ scopeCoordinate ∷ []

mixedCaseDemand : SemanticDemand
mixedCaseDemand =
  semanticDemand
    (generalWhoSaidWhat ∷ historicalProvenance ∷ legalSubmissionRole ∷ [])
    ( discourseCoordinate
    ∷ referenceCoordinate
    ∷ attributionCoordinate
    ∷ provenanceCoordinate
    ∷ temporalCoordinate
    ∷ documentContextCoordinate
    ∷ [])
    ( "general:discourse+reference+attribution"
    ∷ "historical:provenance+temporal"
    ∷ "legal-discourse-role:document-context"
    ∷ [])
    "simultaneous general + historical + legal-discourse demand over one carrier"

------------------------------------------------------------------------
-- Required-axis evidence is coordinate-local.
------------------------------------------------------------------------

data CoordinateEvidenceState : Set where
  coordinateResolved
  coordinateMissing
  coordinateConflicting
  : CoordinateEvidenceState

coordinateSupport : CoordinateEvidenceState → Support.SupportSquare
coordinateSupport coordinateResolved = Support.supportSquare true false
coordinateSupport coordinateMissing = Support.supportSquare false false
coordinateSupport coordinateConflicting = Support.supportSquare true true

record RequiredCoordinateEvidence
    (consumer : Consumer.ConsumerKind)
    (query : SemanticQuery)
    (coordinate : SemanticCoordinate) : Set where
  constructor requiredCoordinateEvidence
  field
    required : Requires consumer query coordinate
    evidenceState : CoordinateEvidenceState
    evidenceReference : String

open RequiredCoordinateEvidence public

missingAuthorityForApplicability :
  RequiredCoordinateEvidence
    Consumer.legalConsumer legalApplicabilityQuery authorityCoordinate
missingAuthorityForApplicability =
  requiredCoordinateEvidence
    legalApplicabilityNeedsAuthority
    coordinateMissing
    "authority evidence unresolved for applicability query"

missingAuthorityCannotBeResolvedPositive :
  Support.ResolvedPositive
    (coordinateSupport (evidenceState missingAuthorityForApplicability)) → ⊥
missingAuthorityCannotBeResolvedPositive resolved =
  Support.missingCannotBeResolvedPositive (refl , refl) resolved

------------------------------------------------------------------------
-- Dependency graph from semantic coordinates to consumer-facing products.
--
-- The graph is deliberately sparse.  A changed authority receipt can reopen a
-- legal applicability/liability product without forcing parser syntax or a
-- general who-said-what answer to be recomputed.
------------------------------------------------------------------------

data SemanticArtifact : Set where
  coordinateArtifact : SemanticCoordinate → SemanticArtifact
  generalDiscourseAnswerArtifact
  historicalAnswerArtifact
  legalDiscourseAnswerArtifact
  legalApplicabilityAnswerArtifact
  legalLiabilityAnswerArtifact
  : SemanticArtifact

data SemanticDepends : SemanticArtifact → SemanticArtifact → Set where
  discourseFeedsGeneral :
    SemanticDepends (coordinateArtifact discourseCoordinate) generalDiscourseAnswerArtifact
  referenceFeedsGeneral :
    SemanticDepends (coordinateArtifact referenceCoordinate) generalDiscourseAnswerArtifact
  attributionFeedsGeneral :
    SemanticDepends (coordinateArtifact attributionCoordinate) generalDiscourseAnswerArtifact

  discourseFeedsHistorical :
    SemanticDepends (coordinateArtifact discourseCoordinate) historicalAnswerArtifact
  attributionFeedsHistorical :
    SemanticDepends (coordinateArtifact attributionCoordinate) historicalAnswerArtifact
  provenanceFeedsHistorical :
    SemanticDepends (coordinateArtifact provenanceCoordinate) historicalAnswerArtifact
  temporalFeedsHistorical :
    SemanticDepends (coordinateArtifact temporalCoordinate) historicalAnswerArtifact

  discourseFeedsLegalDiscourse :
    SemanticDepends (coordinateArtifact discourseCoordinate) legalDiscourseAnswerArtifact
  referenceFeedsLegalDiscourse :
    SemanticDepends (coordinateArtifact referenceCoordinate) legalDiscourseAnswerArtifact
  attributionFeedsLegalDiscourse :
    SemanticDepends (coordinateArtifact attributionCoordinate) legalDiscourseAnswerArtifact
  contextFeedsLegalDiscourse :
    SemanticDepends (coordinateArtifact documentContextCoordinate) legalDiscourseAnswerArtifact

  propositionFeedsApplicability :
    SemanticDepends (coordinateArtifact propositionStatusCoordinate) legalApplicabilityAnswerArtifact
  occurrenceFeedsApplicability :
    SemanticDepends (coordinateArtifact occurrenceCoordinate) legalApplicabilityAnswerArtifact
  evidenceFeedsApplicability :
    SemanticDepends (coordinateArtifact evidenceCoordinate) legalApplicabilityAnswerArtifact
  contextFeedsApplicability :
    SemanticDepends (coordinateArtifact documentContextCoordinate) legalApplicabilityAnswerArtifact
  authorityFeedsApplicability :
    SemanticDepends (coordinateArtifact authorityCoordinate) legalApplicabilityAnswerArtifact
  jurisdictionFeedsApplicability :
    SemanticDepends (coordinateArtifact jurisdictionCoordinate) legalApplicabilityAnswerArtifact
  scopeFeedsApplicability :
    SemanticDepends (coordinateArtifact scopeCoordinate) legalApplicabilityAnswerArtifact

  applicabilityFeedsLiability :
    SemanticDepends legalApplicabilityAnswerArtifact legalLiabilityAnswerArtifact
  violationFeedsLiability :
    SemanticDepends (coordinateArtifact violationCoordinate) legalLiabilityAnswerArtifact
  roleFeedsLiability :
    SemanticDepends (coordinateArtifact legalRoleCoordinate) legalLiabilityAnswerArtifact
  authorityFeedsLiability :
    SemanticDepends (coordinateArtifact authorityCoordinate) legalLiabilityAnswerArtifact
  jurisdictionFeedsLiability :
    SemanticDepends (coordinateArtifact jurisdictionCoordinate) legalLiabilityAnswerArtifact

------------------------------------------------------------------------
-- Exact selective-reopening specimens using the existing generic closure.
------------------------------------------------------------------------

authorityChangeReopensApplicability :
  Closure.ReopeningObligation
    SemanticDepends
    (coordinateArtifact authorityCoordinate)
    legalApplicabilityAnswerArtifact
authorityChangeReopensApplicability =
  Closure.oneEdgeCreatesReopeningObligation authorityFeedsApplicability

authorityChangeReopensLiabilityTransitively :
  Closure.ReopeningObligation
    SemanticDepends
    (coordinateArtifact authorityCoordinate)
    legalLiabilityAnswerArtifact
authorityChangeReopensLiabilityTransitively =
  Closure.obligationsCompose
    authorityChangeReopensApplicability
    (Closure.oneEdgeCreatesReopeningObligation applicabilityFeedsLiability)

provenanceChangeReopensHistoricalAnswer :
  Closure.ReopeningObligation
    SemanticDepends
    (coordinateArtifact provenanceCoordinate)
    historicalAnswerArtifact
provenanceChangeReopensHistoricalAnswer =
  Closure.oneEdgeCreatesReopeningObligation provenanceFeedsHistorical

contextChangeReopensLegalDiscourseAnswer :
  Closure.ReopeningObligation
    SemanticDepends
    (coordinateArtifact documentContextCoordinate)
    legalDiscourseAnswerArtifact
contextChangeReopensLegalDiscourseAnswer =
  Closure.oneEdgeCreatesReopeningObligation contextFeedsLegalDiscourse

------------------------------------------------------------------------
-- Hard boundaries / least privilege.
------------------------------------------------------------------------

data ConsumerKindAloneFixesRequirements : Set where
data LegalConsumerAlwaysNeedsApplicability : Set where
data UnrequestedCoordinateMustResolve : Set where
data EvidenceOnOneCoordinateFillsAnother : Set where
data AuthorityChangeReparsesSyntax : Set where
data BroaderDemandRewritesSemanticCarrier : Set where
data OneConsumerRequirementErasesAnother : Set where

consumerKindAloneDoesNotFixRequirements :
  ConsumerKindAloneFixesRequirements → ⊥
consumerKindAloneDoesNotFixRequirements ()

legalConsumerDoesNotAlwaysNeedApplicability :
  LegalConsumerAlwaysNeedsApplicability → ⊥
legalConsumerDoesNotAlwaysNeedApplicability ()

unrequestedCoordinateDoesNotCountAsFailure :
  UnrequestedCoordinateMustResolve → ⊥
unrequestedCoordinateDoesNotCountAsFailure ()

evidenceDoesNotCrossFillRequiredCoordinates :
  EvidenceOnOneCoordinateFillsAnother → ⊥
evidenceDoesNotCrossFillRequiredCoordinates ()

authorityChangeDoesNotReparseSyntax : AuthorityChangeReparsesSyntax → ⊥
authorityChangeDoesNotReparseSyntax ()

broaderDemandDoesNotRewriteCarrier : BroaderDemandRewritesSemanticCarrier → ⊥
broaderDemandDoesNotRewriteCarrier ()

oneConsumerRequirementDoesNotEraseAnother :
  OneConsumerRequirementErasesAnother → ⊥
oneConsumerRequirementDoesNotEraseAnother ()

record ConsumerQueryCoordinateBoundary : Set where
  constructor consumerQueryCoordinateBoundary
  field
    requirementsAreConsumerAndQueryIndexed : Bool
    inactiveCoordinatesCountAsFailures : Bool
    multipleRequestsMayActivateJointCoordinates : Bool
    strongOneAxisEvidenceFillsMissingOtherAxis : Bool
    dependencyAffectedProductsMayReopenTransitively : Bool
    unrelatedParserCoordinatesMustReopenAfterAuthorityChange : Bool
    broaderDemandRewritesUnderlyingSemanticCarrier : Bool

canonicalConsumerQueryCoordinateBoundary : ConsumerQueryCoordinateBoundary
canonicalConsumerQueryCoordinateBoundary =
  consumerQueryCoordinateBoundary
    true false true false true false false
