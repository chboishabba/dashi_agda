module DASHI.Cognition.PNF.SensibLawSemanticStatusCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionExact as Constitution
import DASHI.Reasoning.SpacyExecutableSemanticRuleBankExact as RuleBank
import DASHI.Cognition.PNF.SensibLawRelationAttachmentCandidateProducerExact as Relation
import DASHI.Cognition.PNF.SensibLawLegalSemanticAdmissionFrontierExact as Admission
import DASHI.Cognition.PNF.ContextualFractranDirectDeltaAdapterExact as Contextual

data ProducerClass : Set where
  parserShapeProducer structuralCompositionProducer bindingAccessibilityProducer
  attributionProducer evidenceProducer temporalProducer scopeResolutionProducer
  documentContextProducer legalJurisdictionProducer legalSourceAuthorityProducer
  legalTypedMeetProducer governedAdmissionProducer : ProducerClass

data StatusAxis : Set where
  participantRoleAxis referentKindAxis identityAxis antecedentAxis occurrenceAxis
  propositionAxis attributionAxis evidenceAxis modalityAxis temporalAxis conditionAxis
  scopeCandidateAxis resolvedScopeAxis documentContextAxis jurisdictionCandidateAxis
  resolvedLegalJurisdictionAxis semanticAdmissionAuthorityAxis legalSourceAuthorityAxis
  applicabilityAxis violationAxis liabilityAxis burdenAxis judicialDiscourseAxis
  normativeRelationAxis : StatusAxis

record AxisPopulationReceipt : Set where
  constructor axisPopulationReceipt
  field
    producer : ProducerClass
    axis : StatusAxis
    candidateOnly : Bool
    requiresCompositeEvidence : Bool
    requiresContextResolution : Bool
    requiresGovernedAdmissionForClosure : Bool
    producerReference : String
open AxisPopulationReceipt public

parserParticipantCandidate : AxisPopulationReceipt
parserParticipantCandidate = axisPopulationReceipt parserShapeProducer participantRoleAxis true true true true "SpacyExecutableSemanticRuleBankExact"
structuralReferentCandidate : AxisPopulationReceipt
structuralReferentCandidate = axisPopulationReceipt structuralCompositionProducer referentKindAxis true true true true "SensibLawSpacyCompositionOnlySemanticConstitutionExact"
bindingAntecedentCandidate : AxisPopulationReceipt
bindingAntecedentCandidate = axisPopulationReceipt bindingAccessibilityProducer antecedentAxis true true true true "set-valued binding/accessibility candidate set"
bindingIdentityCandidate : AxisPopulationReceipt
bindingIdentityCandidate = axisPopulationReceipt bindingAccessibilityProducer identityAxis true true true true "binding candidate membership; identity closure forbidden"
occurrenceCandidateRequiresStatusEvidence : AxisPopulationReceipt
occurrenceCandidateRequiresStatusEvidence = axisPopulationReceipt structuralCompositionProducer occurrenceAxis true true true true "eventuality mention plus proposition/evidence status"
propositionCandidateRequiresAttribution : AxisPopulationReceipt
propositionCandidateRequiresAttribution = axisPopulationReceipt attributionProducer propositionAxis true true true true "attribution/status composition"
evidenceCandidateRequiresProvenance : AxisPopulationReceipt
evidenceCandidateRequiresProvenance = axisPopulationReceipt evidenceProducer evidenceAxis true true true true "source/provenance evidence composition"
temporalCandidateRequiresAnchor : AxisPopulationReceipt
temporalCandidateRequiresAnchor = axisPopulationReceipt temporalProducer temporalAxis true true true true "temporal qualification/anchor composition"
structuralScopeCandidateRequiresComposition : AxisPopulationReceipt
structuralScopeCandidateRequiresComposition = axisPopulationReceipt structuralCompositionProducer scopeCandidateAxis true true true true "parser/dependency composition may expose scope candidates only"
resolvedScopeRequiresCompositeReceipt : AxisPopulationReceipt
resolvedScopeRequiresCompositeReceipt = axisPopulationReceipt scopeResolutionProducer resolvedScopeAxis false true true false "SensibLawScopeCompositionBidiExact joint scope receipt"
documentContextCandidateRequiresStructure : AxisPopulationReceipt
documentContextCandidateRequiresStructure = axisPopulationReceipt documentContextProducer documentContextAxis true true true true "typed document/region/case context composition"
legalJurisdictionCandidateRequiresContext : AxisPopulationReceipt
legalJurisdictionCandidateRequiresContext = axisPopulationReceipt documentContextProducer jurisdictionCandidateAxis true true true true "document/geographic/legal-system context may propose jurisdiction candidates only"
resolvedLegalJurisdictionRequiresSystemWeld : AxisPopulationReceipt
resolvedLegalJurisdictionRequiresSystemWeld = axisPopulationReceipt legalJurisdictionProducer resolvedLegalJurisdictionAxis false true true false "CaseFrame legalSystemId + LegalSystem systemId + resolved legal jurisdiction kind"
legalSourceAuthorityRequiresSystemAndValidity : AxisPopulationReceipt
legalSourceAuthorityRequiresSystemAndValidity = axisPopulationReceipt legalSourceAuthorityProducer legalSourceAuthorityAxis true true true true "SensibLawOntologyTopology LegalSource + source system + validity interval; legal authority not inferred from semantic admission"
legalApplicabilityCandidateRequiresTypedMeet : AxisPopulationReceipt
legalApplicabilityCandidateRequiresTypedMeet = axisPopulationReceipt legalTypedMeetProducer applicabilityAxis true true true true "legal typed meet consumes resolved jurisdiction/authority/scope plus event/wrong/evidence coordinates"
admissionClosureReceipt : AxisPopulationReceipt
admissionClosureReceipt = axisPopulationReceipt governedAdmissionProducer semanticAdmissionAuthorityAxis false true true false "SensibLawLegalSemanticAdmissionFrontierExact semantic resolution/admission authority only"

ruleBankModalEdgeDoesNotCreateTheorem : RuleBank.modalAuxiliaryCreatesModalTheorem RuleBank.canonicalExecutableSemanticRuleBoundary ≡ false
ruleBankModalEdgeDoesNotCreateTheorem = refl
ruleBankRelativeClauseNeedsCompositeEvidence : RuleBank.relativeClauseMayRequireCompositeEvidence RuleBank.canonicalExecutableSemanticRuleBoundary ≡ true
ruleBankRelativeClauseNeedsCompositeEvidence = refl
ruleBankConditionalNeedsCompositeEvidence : RuleBank.conditionalMayRequireCompositeEvidence RuleBank.canonicalExecutableSemanticRuleBoundary ≡ true
ruleBankConditionalNeedsCompositeEvidence = refl
relationProducerCannotChooseLegalRole : Relation.parserLabelAloneChoosesLegalRole Relation.canonicalRelationResolutionAdmissionBoundary ≡ false
relationProducerCannotChooseLegalRole = refl
noSecondSemanticRuntime : Relation.directRuntimeNeedsSecondRelationalRuntime Relation.canonicalRelationResolutionAdmissionBoundary ≡ false
noSecondSemanticRuntime = refl
consumerCanIgnoreFineExecutionIdentity : Relation.consumerParityMayIgnoreFineExecutionIdentity Relation.canonicalRelationResolutionAdmissionBoundary ≡ true
consumerCanIgnoreFineExecutionIdentity = refl

record StatusQualificationReceipt : Set where
  constructor statusQualificationReceipt
  field
    sourceFibre : Constitution.SemanticCandidateFibre
    statusState : Status.SemanticCommitmentState
    parserRowsReused : Bool
    secondParserRunRequired : Bool
    regexSemanticEvidenceUsed : Bool
    lexicalSurfaceOracleUsed : Bool
open StatusQualificationReceipt public

record CrossPollinationBoundary : Set where
  constructor crossPollinationBoundary
  field
    oldObligationExtractorMayPromoteStatus : Bool
    oldObligationExtractorMayPromoteStatusIsFalse : oldObligationExtractorMayPromoteStatus ≡ false
    legalIRMayRediscoverSemanticsIndependently : Bool
    legalIRMayRediscoverSemanticsIndependentlyIsFalse : legalIRMayRediscoverSemanticsIndependently ≡ false
    candidateStatusMayRemainUnresolved : Bool
    candidateStatusMayRemainUnresolvedIsTrue : candidateStatusMayRemainUnresolved ≡ true
    oneConsumerProjectionMayIgnoreOtherAxes : Bool
    oneConsumerProjectionMayIgnoreOtherAxesIsTrue : oneConsumerProjectionMayIgnoreOtherAxes ≡ true
    omittedAxisMustRemainRecoverableOrResidual : Bool
    omittedAxisMustRemainRecoverableOrResidualIsTrue : omittedAxisMustRemainRecoverableOrResidual ≡ true
canonicalCrossPollinationBoundary : CrossPollinationBoundary
canonicalCrossPollinationBoundary = crossPollinationBoundary false refl false refl true refl true refl true refl

data ReportingVerbMakesEmbeddedPropositionTrue : Set where
data QuotedSpeakerIsDocumentAuthor : Set where
data GeographicLocationIsLegalJurisdiction : Set where
data LegalAuthorityIsPromotionAuthority : Set where
data ParserScopeCandidateIsResolvedScope : Set where
data JurisdictionCandidateIsResolvedLegalJurisdiction : Set where
data FoundAsFactIsUniversalTruth : Set where
data NormativeRelationIsModalSurface : Set where
data BurdenBearerIsSyntacticSubject : Set where
reportingDoesNotMakeEmbeddedTruth : ReportingVerbMakesEmbeddedPropositionTrue → ⊥
reportingDoesNotMakeEmbeddedTruth ()
quotedSpeakerNeedNotBeAuthor : QuotedSpeakerIsDocumentAuthor → ⊥
quotedSpeakerNeedNotBeAuthor ()
locationDoesNotDetermineLegalJurisdiction : GeographicLocationIsLegalJurisdiction → ⊥
locationDoesNotDetermineLegalJurisdiction ()
legalAuthorityDoesNotEqualPromotionAuthority : LegalAuthorityIsPromotionAuthority → ⊥
legalAuthorityDoesNotEqualPromotionAuthority ()
parserScopeCandidateDoesNotEqualResolvedScope : ParserScopeCandidateIsResolvedScope → ⊥
parserScopeCandidateDoesNotEqualResolvedScope ()
jurisdictionCandidateDoesNotEqualResolvedLegalJurisdiction : JurisdictionCandidateIsResolvedLegalJurisdiction → ⊥
jurisdictionCandidateDoesNotEqualResolvedLegalJurisdiction ()
foundAsFactDoesNotMeanUniversalTruth : FoundAsFactIsUniversalTruth → ⊥
foundAsFactDoesNotMeanUniversalTruth ()
normativeRelationNotRawModalSurface : NormativeRelationIsModalSurface → ⊥
normativeRelationNotRawModalSurface ()
burdenBearerNotSyntacticSubject : BurdenBearerIsSyntacticSubject → ⊥
burdenBearerNotSyntacticSubject ()
existingAdmissionStillSeparate : Admission.ParserCandidateAloneAuthorizesAdmission → ⊥
existingAdmissionStillSeparate = Admission.parserCandidateAloneCannotAuthorizeAdmission
