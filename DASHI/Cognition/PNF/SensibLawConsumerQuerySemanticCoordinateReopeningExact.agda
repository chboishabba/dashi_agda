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
  semanticAdmissionAuthorityCoordinate
  legalSourceAuthorityCoordinate
  jurisdictionCoordinate
  legalRoleCoordinate
  applicabilityCoordinate
  violationCoordinate
  liabilityCoordinate
  : SemanticCoordinate

------------------------------------------------------------------------
-- Proof-bearing requirement relation.
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
  legalApplicabilityNeedsLegalSourceAuthority :
    Requires Consumer.legalConsumer legalApplicabilityQuery legalSourceAuthorityCoordinate
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
  legalLiabilityNeedsLegalSourceAuthority :
    Requires Consumer.legalConsumer legalLiabilityQuery legalSourceAuthorityCoordinate
  legalLiabilityNeedsJurisdiction :
    Requires Consumer.legalConsumer legalLiabilityQuery jurisdictionCoordinate

record DemandRequest : Set where
  constructor demandRequest
  field
    consumer : Consumer.ConsumerKind
    query : SemanticQuery
    requestReference : String

open DemandRequest public

record ActiveRequirement : Set where
  constructor activeRequirement
  field
    requiredConsumer : Consumer.ConsumerKind
    requiredQuery : SemanticQuery
    coordinate : SemanticCoordinate
    requirement : Requires requiredConsumer requiredQuery coordinate
    requirementReference : String

open ActiveRequirement public

record SemanticDemand : Set where
  constructor semanticDemand
  field
    requests : List DemandRequest
    activeRequirements : List ActiveRequirement
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
  ∷ documentContextCoordinate ∷ legalSourceAuthorityCoordinate
  ∷ jurisdictionCoordinate ∷ scopeCoordinate ∷ []

mixedCaseDemand : SemanticDemand
mixedCaseDemand =
  semanticDemand
    (generalWhoSaidWhat ∷ historicalProvenance ∷ legalSubmissionRole ∷ [])
    ( activeRequirement Consumer.generalSemanticConsumer whoSaidWhatQuery
        discourseCoordinate whoNeedsDiscourse "general who-said-what needs discourse"
    ∷ activeRequirement Consumer.generalSemanticConsumer whoSaidWhatQuery
        referenceCoordinate whoNeedsReference "general who-said-what needs reference"
    ∷ activeRequirement Consumer.generalSemanticConsumer whoSaidWhatQuery
        attributionCoordinate whoNeedsAttribution "general who-said-what needs attribution"
    ∷ activeRequirement Consumer.historicalConsumer provenanceHistoryQuery
        discourseCoordinate historyNeedsDiscourse "historical query needs discourse"
    ∷ activeRequirement Consumer.historicalConsumer provenanceHistoryQuery
        attributionCoordinate historyNeedsAttribution "historical query needs attribution"
    ∷ activeRequirement Consumer.historicalConsumer provenanceHistoryQuery
        provenanceCoordinate historyNeedsProvenance "historical query needs provenance"
    ∷ activeRequirement Consumer.historicalConsumer provenanceHistoryQuery
        temporalCoordinate historyNeedsTemporal "historical query needs temporal relation"
    ∷ activeRequirement Consumer.legalConsumer legalDiscourseRoleQuery
        discourseCoordinate legalRoleNeedsDiscourse "legal discourse-role query needs discourse"
    ∷ activeRequirement Consumer.legalConsumer legalDiscourseRoleQuery
        referenceCoordinate legalRoleNeedsReference "legal discourse-role query needs reference"
    ∷ activeRequirement Consumer.legalConsumer legalDiscourseRoleQuery
        attributionCoordinate legalRoleNeedsAttribution "legal discourse-role query needs attribution"
    ∷ activeRequirement Consumer.legalConsumer legalDiscourseRoleQuery
        documentContextCoordinate legalRoleNeedsDocumentContext "legal discourse-role query needs document context"
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

missingLegalSourceAuthorityForApplicability :
  RequiredCoordinateEvidence
    Consumer.legalConsumer legalApplicabilityQuery legalSourceAuthorityCoordinate
missingLegalSourceAuthorityForApplicability =
  requiredCoordinateEvidence
    legalApplicabilityNeedsLegalSourceAuthority
    coordinateMissing
    "legal-source authority evidence unresolved for applicability query"

missingLegalSourceAuthorityCannotBeResolvedPositive :
  Support.ResolvedPositive
    (coordinateSupport (evidenceState missingLegalSourceAuthorityForApplicability)) → ⊥
missingLegalSourceAuthorityCannotBeResolvedPositive resolved =
  Support.missingCannotBeResolvedPositive (refl , refl) resolved

------------------------------------------------------------------------
-- Dependency graph from semantic coordinates to consumer-facing products.
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
  legalSourceAuthorityFeedsApplicability :
    SemanticDepends (coordinateArtifact legalSourceAuthorityCoordinate) legalApplicabilityAnswerArtifact
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
  legalSourceAuthorityFeedsLiability :
    SemanticDepends (coordinateArtifact legalSourceAuthorityCoordinate) legalLiabilityAnswerArtifact
  jurisdictionFeedsLiability :
    SemanticDepends (coordinateArtifact jurisdictionCoordinate) legalLiabilityAnswerArtifact

------------------------------------------------------------------------
-- Exact selective-reopening specimens using the existing generic closure.
------------------------------------------------------------------------

legalSourceAuthorityChangeReopensApplicability :
  Closure.ReopeningObligation
    SemanticDepends
    (coordinateArtifact legalSourceAuthorityCoordinate)
    legalApplicabilityAnswerArtifact
legalSourceAuthorityChangeReopensApplicability =
  Closure.oneEdgeCreatesReopeningObligation legalSourceAuthorityFeedsApplicability

legalSourceAuthorityChangeReopensLiabilityTransitively :
  Closure.ReopeningObligation
    SemanticDepends
    (coordinateArtifact legalSourceAuthorityCoordinate)
    legalLiabilityAnswerArtifact
legalSourceAuthorityChangeReopensLiabilityTransitively =
  Closure.obligationsCompose
    legalSourceAuthorityChangeReopensApplicability
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
data SemanticAdmissionAuthorityPaysLegalSourceAuthority : Set where

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

semanticAdmissionAuthorityDoesNotPayLegalSourceAuthority :
  SemanticAdmissionAuthorityPaysLegalSourceAuthority → ⊥
semanticAdmissionAuthorityDoesNotPayLegalSourceAuthority ()

record ConsumerQueryCoordinateBoundary : Set where
  constructor consumerQueryCoordinateBoundary
  field
    requirementsAreConsumerAndQueryIndexed : Bool
    inactiveCoordinatesCountAsFailures : Bool
    multipleRequestsMayActivateJointCoordinates : Bool
    activeRequirementsCarryProofWitnesses : Bool
    semanticAdmissionAndLegalSourceAuthorityDistinct : Bool
    strongOneAxisEvidenceFillsMissingOtherAxis : Bool
    dependencyAffectedProductsMayReopenTransitively : Bool
    unrelatedParserCoordinatesMustReopenAfterAuthorityChange : Bool
    broaderDemandRewritesUnderlyingSemanticCarrier : Bool

canonicalConsumerQueryCoordinateBoundary : ConsumerQueryCoordinateBoundary
canonicalConsumerQueryCoordinateBoundary =
  consumerQueryCoordinateBoundary
    true false true true true false true false false
