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

data SemanticQuery : Set where
  parseStructureQuery whoSaidWhatQuery provenanceHistoryQuery discourseContextQuery
  legalDiscourseRoleQuery legalApplicabilityQuery legalLiabilityQuery
  customQuery : String → SemanticQuery

data SemanticCoordinate : Set where
  syntaxCoordinate discourseCoordinate referenceCoordinate attributionCoordinate
  provenanceCoordinate temporalCoordinate evidenceCandidateCoordinate
  resolvedLegalEvidenceCoordinate scopeCandidateCoordinate resolvedScopeCoordinate
  propositionStatusCoordinate occurrenceCoordinate documentContextCoordinate
  jurisdictionCandidateCoordinate resolvedLegalJurisdictionCoordinate
  semanticAdmissionAuthorityCoordinate legalSourceAuthorityCoordinate
  legalRoleCoordinate applicabilityCoordinate violationCoordinate liabilityCoordinate
  : SemanticCoordinate

data Requires : Consumer.ConsumerKind → SemanticQuery → SemanticCoordinate → Set where
  parseNeedsSyntax : ∀ {consumer} → Requires consumer parseStructureQuery syntaxCoordinate
  whoNeedsDiscourse : ∀ {consumer} → Requires consumer whoSaidWhatQuery discourseCoordinate
  whoNeedsReference : ∀ {consumer} → Requires consumer whoSaidWhatQuery referenceCoordinate
  whoNeedsAttribution : ∀ {consumer} → Requires consumer whoSaidWhatQuery attributionCoordinate
  historyNeedsDiscourse : ∀ {consumer} → Requires consumer provenanceHistoryQuery discourseCoordinate
  historyNeedsAttribution : ∀ {consumer} → Requires consumer provenanceHistoryQuery attributionCoordinate
  historyNeedsProvenance : ∀ {consumer} → Requires consumer provenanceHistoryQuery provenanceCoordinate
  historyNeedsTemporal : ∀ {consumer} → Requires consumer provenanceHistoryQuery temporalCoordinate
  contextNeedsDiscourse : ∀ {consumer} → Requires consumer discourseContextQuery discourseCoordinate
  contextNeedsDocumentContext : ∀ {consumer} → Requires consumer discourseContextQuery documentContextCoordinate
  legalRoleNeedsDiscourse : Requires Consumer.legalConsumer legalDiscourseRoleQuery discourseCoordinate
  legalRoleNeedsReference : Requires Consumer.legalConsumer legalDiscourseRoleQuery referenceCoordinate
  legalRoleNeedsAttribution : Requires Consumer.legalConsumer legalDiscourseRoleQuery attributionCoordinate
  legalRoleNeedsDocumentContext : Requires Consumer.legalConsumer legalDiscourseRoleQuery documentContextCoordinate
  legalApplicabilityNeedsProposition : Requires Consumer.legalConsumer legalApplicabilityQuery propositionStatusCoordinate
  legalApplicabilityNeedsOccurrence : Requires Consumer.legalConsumer legalApplicabilityQuery occurrenceCoordinate
  legalApplicabilityNeedsResolvedEvidence : Requires Consumer.legalConsumer legalApplicabilityQuery resolvedLegalEvidenceCoordinate
  legalApplicabilityNeedsContext : Requires Consumer.legalConsumer legalApplicabilityQuery documentContextCoordinate
  legalApplicabilityNeedsLegalSourceAuthority : Requires Consumer.legalConsumer legalApplicabilityQuery legalSourceAuthorityCoordinate
  legalApplicabilityNeedsResolvedJurisdiction : Requires Consumer.legalConsumer legalApplicabilityQuery resolvedLegalJurisdictionCoordinate
  legalApplicabilityNeedsResolvedScope : Requires Consumer.legalConsumer legalApplicabilityQuery resolvedScopeCoordinate
  legalLiabilityNeedsApplicability : Requires Consumer.legalConsumer legalLiabilityQuery applicabilityCoordinate
  legalLiabilityNeedsViolation : Requires Consumer.legalConsumer legalLiabilityQuery violationCoordinate
  legalLiabilityNeedsLegalRole : Requires Consumer.legalConsumer legalLiabilityQuery legalRoleCoordinate
  legalLiabilityNeedsResolvedEvidence : Requires Consumer.legalConsumer legalLiabilityQuery resolvedLegalEvidenceCoordinate
  legalLiabilityNeedsLegalSourceAuthority : Requires Consumer.legalConsumer legalLiabilityQuery legalSourceAuthorityCoordinate
  legalLiabilityNeedsResolvedJurisdiction : Requires Consumer.legalConsumer legalLiabilityQuery resolvedLegalJurisdictionCoordinate

record DemandRequest : Set where
  constructor demandRequest
  field consumer : Consumer.ConsumerKind; query : SemanticQuery; requestReference : String
open DemandRequest public
record ActiveRequirement : Set where
  constructor activeRequirement
  field requiredConsumer : Consumer.ConsumerKind; requiredQuery : SemanticQuery; coordinate : SemanticCoordinate; requirement : Requires requiredConsumer requiredQuery coordinate; requirementReference : String
open ActiveRequirement public
record SemanticDemand : Set where
  constructor semanticDemand
  field requests : List DemandRequest; activeRequirements : List ActiveRequirement; demandReference : String
open SemanticDemand public

generalWhoSaidWhat = demandRequest Consumer.generalSemanticConsumer whoSaidWhatQuery "general consumer asks who said what"
legalWhoSaidWhat = demandRequest Consumer.legalConsumer whoSaidWhatQuery "legal consumer asks only who said what"
legalSubmissionRole = demandRequest Consumer.legalConsumer legalDiscourseRoleQuery "legal consumer asks discourse role"
historicalProvenance = demandRequest Consumer.historicalConsumer provenanceHistoryQuery "historical consumer asks provenance/time"
legalApplicability = demandRequest Consumer.legalConsumer legalApplicabilityQuery "legal consumer asks governed applicability"
legalLiability = demandRequest Consumer.legalConsumer legalLiabilityQuery "legal consumer asks liability"

whoSaidWhatRequirements = discourseCoordinate ∷ referenceCoordinate ∷ attributionCoordinate ∷ []
legalDiscourseRoleRequirements = discourseCoordinate ∷ referenceCoordinate ∷ attributionCoordinate ∷ documentContextCoordinate ∷ []
historicalRequirements = discourseCoordinate ∷ attributionCoordinate ∷ provenanceCoordinate ∷ temporalCoordinate ∷ []
legalApplicabilityRequirements = propositionStatusCoordinate ∷ occurrenceCoordinate ∷ resolvedLegalEvidenceCoordinate ∷ documentContextCoordinate ∷ legalSourceAuthorityCoordinate ∷ resolvedLegalJurisdictionCoordinate ∷ resolvedScopeCoordinate ∷ []

mixedCaseDemand = semanticDemand
  (generalWhoSaidWhat ∷ historicalProvenance ∷ legalSubmissionRole ∷ [])
  ( activeRequirement Consumer.generalSemanticConsumer whoSaidWhatQuery discourseCoordinate whoNeedsDiscourse "general discourse"
  ∷ activeRequirement Consumer.generalSemanticConsumer whoSaidWhatQuery referenceCoordinate whoNeedsReference "general reference"
  ∷ activeRequirement Consumer.generalSemanticConsumer whoSaidWhatQuery attributionCoordinate whoNeedsAttribution "general attribution"
  ∷ activeRequirement Consumer.historicalConsumer provenanceHistoryQuery discourseCoordinate historyNeedsDiscourse "history discourse"
  ∷ activeRequirement Consumer.historicalConsumer provenanceHistoryQuery attributionCoordinate historyNeedsAttribution "history attribution"
  ∷ activeRequirement Consumer.historicalConsumer provenanceHistoryQuery provenanceCoordinate historyNeedsProvenance "history provenance"
  ∷ activeRequirement Consumer.historicalConsumer provenanceHistoryQuery temporalCoordinate historyNeedsTemporal "history temporal"
  ∷ activeRequirement Consumer.legalConsumer legalDiscourseRoleQuery discourseCoordinate legalRoleNeedsDiscourse "legal discourse"
  ∷ activeRequirement Consumer.legalConsumer legalDiscourseRoleQuery referenceCoordinate legalRoleNeedsReference "legal reference"
  ∷ activeRequirement Consumer.legalConsumer legalDiscourseRoleQuery attributionCoordinate legalRoleNeedsAttribution "legal attribution"
  ∷ activeRequirement Consumer.legalConsumer legalDiscourseRoleQuery documentContextCoordinate legalRoleNeedsDocumentContext "legal context" ∷ [])
  "simultaneous general + historical + legal-discourse demand"

data CoordinateEvidenceState : Set where coordinateResolved coordinateMissing coordinateConflicting : CoordinateEvidenceState
coordinateSupport coordinateResolved = Support.supportSquare true false
coordinateSupport coordinateMissing = Support.supportSquare false false
coordinateSupport coordinateConflicting = Support.supportSquare true true
record RequiredCoordinateEvidence (consumer : Consumer.ConsumerKind) (query : SemanticQuery) (coordinate : SemanticCoordinate) : Set where
  constructor requiredCoordinateEvidence
  field required : Requires consumer query coordinate; evidenceState : CoordinateEvidenceState; evidenceReference : String
open RequiredCoordinateEvidence public

missingLegalSourceAuthorityForApplicability = requiredCoordinateEvidence legalApplicabilityNeedsLegalSourceAuthority coordinateMissing "legal-source authority unresolved"
missingLegalSourceAuthorityCannotBeResolvedPositive : Support.ResolvedPositive (coordinateSupport (evidenceState missingLegalSourceAuthorityForApplicability)) → ⊥
missingLegalSourceAuthorityCannotBeResolvedPositive resolved = Support.missingCannotBeResolvedPositive (refl , refl) resolved

data SemanticArtifact : Set where
  coordinateArtifact : SemanticCoordinate → SemanticArtifact
  generalDiscourseAnswerArtifact historicalAnswerArtifact legalDiscourseAnswerArtifact legalApplicabilityAnswerArtifact legalLiabilityAnswerArtifact : SemanticArtifact

data SemanticDepends : SemanticArtifact → SemanticArtifact → Set where
  discourseFeedsGeneral : SemanticDepends (coordinateArtifact discourseCoordinate) generalDiscourseAnswerArtifact
  referenceFeedsGeneral : SemanticDepends (coordinateArtifact referenceCoordinate) generalDiscourseAnswerArtifact
  attributionFeedsGeneral : SemanticDepends (coordinateArtifact attributionCoordinate) generalDiscourseAnswerArtifact
  discourseFeedsHistorical : SemanticDepends (coordinateArtifact discourseCoordinate) historicalAnswerArtifact
  attributionFeedsHistorical : SemanticDepends (coordinateArtifact attributionCoordinate) historicalAnswerArtifact
  provenanceFeedsHistorical : SemanticDepends (coordinateArtifact provenanceCoordinate) historicalAnswerArtifact
  temporalFeedsHistorical : SemanticDepends (coordinateArtifact temporalCoordinate) historicalAnswerArtifact
  discourseFeedsLegalDiscourse : SemanticDepends (coordinateArtifact discourseCoordinate) legalDiscourseAnswerArtifact
  referenceFeedsLegalDiscourse : SemanticDepends (coordinateArtifact referenceCoordinate) legalDiscourseAnswerArtifact
  attributionFeedsLegalDiscourse : SemanticDepends (coordinateArtifact attributionCoordinate) legalDiscourseAnswerArtifact
  contextFeedsLegalDiscourse : SemanticDepends (coordinateArtifact documentContextCoordinate) legalDiscourseAnswerArtifact
  propositionFeedsApplicability : SemanticDepends (coordinateArtifact propositionStatusCoordinate) legalApplicabilityAnswerArtifact
  occurrenceFeedsApplicability : SemanticDepends (coordinateArtifact occurrenceCoordinate) legalApplicabilityAnswerArtifact
  resolvedEvidenceFeedsApplicability : SemanticDepends (coordinateArtifact resolvedLegalEvidenceCoordinate) legalApplicabilityAnswerArtifact
  contextFeedsApplicability : SemanticDepends (coordinateArtifact documentContextCoordinate) legalApplicabilityAnswerArtifact
  legalSourceAuthorityFeedsApplicability : SemanticDepends (coordinateArtifact legalSourceAuthorityCoordinate) legalApplicabilityAnswerArtifact
  resolvedJurisdictionFeedsApplicability : SemanticDepends (coordinateArtifact resolvedLegalJurisdictionCoordinate) legalApplicabilityAnswerArtifact
  resolvedScopeFeedsApplicability : SemanticDepends (coordinateArtifact resolvedScopeCoordinate) legalApplicabilityAnswerArtifact
  applicabilityFeedsLiability : SemanticDepends legalApplicabilityAnswerArtifact legalLiabilityAnswerArtifact
  violationFeedsLiability : SemanticDepends (coordinateArtifact violationCoordinate) legalLiabilityAnswerArtifact
  roleFeedsLiability : SemanticDepends (coordinateArtifact legalRoleCoordinate) legalLiabilityAnswerArtifact
  resolvedEvidenceFeedsLiability : SemanticDepends (coordinateArtifact resolvedLegalEvidenceCoordinate) legalLiabilityAnswerArtifact
  legalSourceAuthorityFeedsLiability : SemanticDepends (coordinateArtifact legalSourceAuthorityCoordinate) legalLiabilityAnswerArtifact
  resolvedJurisdictionFeedsLiability : SemanticDepends (coordinateArtifact resolvedLegalJurisdictionCoordinate) legalLiabilityAnswerArtifact

legalSourceAuthorityChangeReopensApplicability = Closure.oneEdgeCreatesReopeningObligation legalSourceAuthorityFeedsApplicability
legalSourceAuthorityChangeReopensLiabilityTransitively = Closure.obligationsCompose legalSourceAuthorityChangeReopensApplicability (Closure.oneEdgeCreatesReopeningObligation applicabilityFeedsLiability)
resolvedScopeChangeReopensApplicability = Closure.oneEdgeCreatesReopeningObligation resolvedScopeFeedsApplicability
resolvedJurisdictionChangeReopensApplicability = Closure.oneEdgeCreatesReopeningObligation resolvedJurisdictionFeedsApplicability
resolvedEvidenceChangeReopensApplicability = Closure.oneEdgeCreatesReopeningObligation resolvedEvidenceFeedsApplicability
provenanceChangeReopensHistoricalAnswer = Closure.oneEdgeCreatesReopeningObligation provenanceFeedsHistorical
contextChangeReopensLegalDiscourseAnswer = Closure.oneEdgeCreatesReopeningObligation contextFeedsLegalDiscourse

data ConsumerKindAloneFixesRequirements : Set where
data LegalConsumerAlwaysNeedsApplicability : Set where
data UnrequestedCoordinateMustResolve : Set where
data EvidenceOnOneCoordinateFillsAnother : Set where
data AuthorityChangeReparsesSyntax : Set where
data BroaderDemandRewritesSemanticCarrier : Set where
data OneConsumerRequirementErasesAnother : Set where
data SemanticAdmissionAuthorityPaysLegalSourceAuthority : Set where
data ScopeCandidatePaysResolvedScope : Set where
data JurisdictionCandidatePaysResolvedLegalJurisdiction : Set where
data EvidenceCandidatePaysResolvedLegalEvidence : Set where
consumerKindAloneDoesNotFixRequirements : ConsumerKindAloneFixesRequirements → ⊥
consumerKindAloneDoesNotFixRequirements ()
legalConsumerDoesNotAlwaysNeedApplicability : LegalConsumerAlwaysNeedsApplicability → ⊥
legalConsumerDoesNotAlwaysNeedApplicability ()
unrequestedCoordinateDoesNotCountAsFailure : UnrequestedCoordinateMustResolve → ⊥
unrequestedCoordinateDoesNotCountAsFailure ()
evidenceDoesNotCrossFillRequiredCoordinates : EvidenceOnOneCoordinateFillsAnother → ⊥
evidenceDoesNotCrossFillRequiredCoordinates ()
authorityChangeDoesNotReparseSyntax : AuthorityChangeReparsesSyntax → ⊥
authorityChangeDoesNotReparseSyntax ()
broaderDemandDoesNotRewriteCarrier : BroaderDemandRewritesSemanticCarrier → ⊥
broaderDemandDoesNotRewriteCarrier ()
oneConsumerRequirementDoesNotEraseAnother : OneConsumerRequirementErasesAnother → ⊥
oneConsumerRequirementDoesNotEraseAnother ()
semanticAdmissionAuthorityDoesNotPayLegalSourceAuthority : SemanticAdmissionAuthorityPaysLegalSourceAuthority → ⊥
semanticAdmissionAuthorityDoesNotPayLegalSourceAuthority ()
scopeCandidateDoesNotPayResolvedScope : ScopeCandidatePaysResolvedScope → ⊥
scopeCandidateDoesNotPayResolvedScope ()
jurisdictionCandidateDoesNotPayResolvedLegalJurisdiction : JurisdictionCandidatePaysResolvedLegalJurisdiction → ⊥
jurisdictionCandidateDoesNotPayResolvedLegalJurisdiction ()
evidenceCandidateDoesNotPayResolvedLegalEvidence : EvidenceCandidatePaysResolvedLegalEvidence → ⊥
evidenceCandidateDoesNotPayResolvedLegalEvidence ()

record ConsumerQueryCoordinateBoundary : Set where
  constructor consumerQueryCoordinateBoundary
  field requirementsAreConsumerAndQueryIndexed inactiveCoordinatesCountAsFailures multipleRequestsMayActivateJointCoordinates activeRequirementsCarryProofWitnesses semanticAdmissionAndLegalSourceAuthorityDistinct evidenceCandidateAndResolvedLegalEvidenceDistinct scopeCandidateAndResolvedScopeDistinct jurisdictionCandidateAndResolvedLegalJurisdictionDistinct strongOneAxisEvidenceFillsMissingOtherAxis dependencyAffectedProductsMayReopenTransitively unrelatedParserCoordinatesMustReopenAfterAuthorityChange broaderDemandRewritesUnderlyingSemanticCarrier : Bool
canonicalConsumerQueryCoordinateBoundary = consumerQueryCoordinateBoundary true false true true true true true true false true false false
