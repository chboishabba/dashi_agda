module DASHI.Law.HerzogColonialWrongTypeElementRequirementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Wrong
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual
import DASHI.Law.AustralianColonialWrongTypeAuthorityReclassificationExact as ColonialWrong
import DASHI.Law.ColonialSemanticPrerequisiteWrongTypeCrossPollinationExact as ColonialPrereq
import DASHI.Law.HerzogColonialWrongTypeCrossSystemBridgeExact as Cross
import DASHI.Law.HerzogUniversalLegalEvidenceBridgeExact as Herzog
import DASHI.Law.SecurityClassificationInputLineageDagExact as Lineage

------------------------------------------------------------------------
-- WRONGTYPE ELEMENT SPECIALISATION
--
-- The analytical WrongType is already owned by
-- AustralianColonialWrongTypeAuthorityReclassificationExact. This file does not
-- create a new wrong. It gives one of its analytical mechanism coordinates a
-- theorem-bearing LegalElement and makes the missing producers explicit.
--
-- This remains an analytical element. It is NOT a current Australian cause of
-- action, statutory element, holding, liability finding, or remedy entitlement.
------------------------------------------------------------------------

colonialWrong : Ontology.WrongType
colonialWrong = ColonialWrong.colonialAuthorityReclassificationWrongType

authorityReclassificationMechanismElement : Elements.LegalElement colonialWrong
authorityReclassificationMechanismElement = Elements.legal-element
  (Ontology.stableId "element:dashi:colonial-authority-reclassification:modern-mechanism")
  Elements.otherElement
  Cross.modernColonialMechanismEstablished
  refl

------------------------------------------------------------------------
-- The element is deliberately factored into three typed requirements.
------------------------------------------------------------------------

data MechanismRequirementKind : Set where
  requiresAuthorityMeaningErasure : MechanismRequirementKind
  requiresOperationalPrerequisite : MechanismRequirementKind
  requiresSameObjectProjectionPowerIncident : MechanismRequirementKind


record OpenMechanismRequirement : Set where
  constructor open-mechanism-requirement
  field
    requirementKind : MechanismRequirementKind
    requiredProposition : Algebra.LegalProposition
    requiredProducer : Cross.TranslationProducer
    residualKind : Residual.LegalResidualKind
    acquisitionRoute : Residual.LegalAcquisitionRoute
    acquisitionRouteIsPreferred : acquisitionRoute ≡ Residual.preferredRoute residualKind
    sourceOrAuthorityReference : String
    currentlyClosed : Bool
    createsElementProofByItself : Bool
    createsElementProofByItselfIsFalse : createsElementProofByItself ≡ false

open OpenMechanismRequirement public

authorityMeaningRequirement : OpenMechanismRequirement
authorityMeaningRequirement = open-mechanism-requirement
  requiresAuthorityMeaningErasure
  Cross.modernAuthorityErasureObserved
  Cross.beforeAfterAuthorityMeaningProducer
  Residual.missingRelationalFeature
  Residual.obtainFactualEvidence refl
  "Requires source-bounded before/after Country/community-authority/political-meaning comparison in the Herzog classification lineage."
  false
  false refl

operationalPrerequisiteRequirement : OpenMechanismRequirement
operationalPrerequisiteRequirement = open-mechanism-requirement
  requiresOperationalPrerequisite
  Cross.authorityErasureOperationalPrerequisite
  Cross.operationalPowerPrerequisiteProducer
  Residual.missingInstitutionalConstraint
  Residual.inspectJudicialReasons refl
  "Requires the power/prerequisite rule showing that erasure or subordination was necessary to the asserted public-order power/tactic; semantic broadening alone is insufficient."
  false
  false refl

sameObjectIncidentRequirement : OpenMechanismRequirement
sameObjectIncidentRequirement = open-mechanism-requirement
  requiresSameObjectProjectionPowerIncident
  Cross.sameObjectProjectionPowerIncidentClosed
  Cross.sameObjectIncidentWeldProducer
  Residual.missingFactualFeature
  Residual.obtainFactualEvidence refl
  "Requires the exact classification -> order -> unit -> field tactic -> incident same-object lineage."
  false
  false refl

------------------------------------------------------------------------
-- A candidate rule shape is represented independently from legal authority.
-- We do not manufacture an Algebra.LegalRule until a suitable authority/source
-- role for this analytical inference is explicitly supplied.
------------------------------------------------------------------------

record AnalyticalMechanismRuleObligation : Set where
  constructor analytical-mechanism-rule-obligation
  field
    premiseA premiseB premiseC : Algebra.LegalProposition
    targetElement : Algebra.LegalProposition
    intendedInference : String
    sourceAttributionConstitution : String
    ruleAuthorityRecovered : Bool
    ruleAuthorityRecoveredIsFalse : ruleAuthorityRecovered ≡ false

open AnalyticalMechanismRuleObligation public

currentAnalyticalMechanismRuleObligation : AnalyticalMechanismRuleObligation
currentAnalyticalMechanismRuleObligation = analytical-mechanism-rule-obligation
  Cross.modernAuthorityErasureObserved
  Cross.authorityErasureOperationalPrerequisite
  Cross.sameObjectProjectionPowerIncidentClosed
  Cross.modernColonialMechanismEstablished
  "If all three separately sourced analytical coordinates close, compile a DASHI analytical mechanism proposition without promoting it to municipal liability."
  "External source propositions remain in the AustralianColonialPrimarySourceAttribution / Herzog provenance owners; this inference is DASHI synthesis."
  false refl

------------------------------------------------------------------------
-- Current finite state: no analytical rule is admitted and no translated
-- analytical facts have been paid. The WrongType element is therefore not
-- reachable merely because the post-hoc Herzog narrative is present.
------------------------------------------------------------------------

currentAnalyticalFacts : Algebra.FactSet
currentAnalyticalFacts = Algebra.fact-set []

currentAnalyticalGraph : Algebra.LegalGraph
currentAnalyticalGraph = Algebra.legal-graph [] []

currentMechanismElementUnreachable :
  Search.reachable 1 currentAnalyticalGraph currentAnalyticalFacts
    (Elements.proposition authorityReclassificationMechanismElement) ≡ false
currentMechanismElementUnreachable = refl

postHocHerzogFactStillCannotReachColonialElement :
  Search.reachable 1 currentAnalyticalGraph
    (Algebra.fact-set (Herzog.postHocNarrativeObserved ∷ []))
    (Elements.proposition authorityReclassificationMechanismElement) ≡ false
postHocHerzogFactStillCannotReachColonialElement = refl

------------------------------------------------------------------------
-- Exact BIDI producer routing from the analytical consumer.
------------------------------------------------------------------------

data ColonialElementConsumerNeed : Set where
  needClassificationContent : ColonialElementConsumerNeed
  needAuthorityMeaningComparison : ColonialElementConsumerNeed
  needOperationalPrerequisite : ColonialElementConsumerNeed
  needIncidentSameObjectWeld : ColonialElementConsumerNeed
  needAnalyticalElementProof : ColonialElementConsumerNeed
  needWrongTypeApplicability : ColonialElementConsumerNeed
  needWrongTypeViolation : ColonialElementConsumerNeed
  needWrongTypeLiability : ColonialElementConsumerNeed


data ColonialElementProducer : Set where
  classificationContentProducer : ColonialElementProducer
  authorityMeaningProducer : ColonialElementProducer
  powerPrerequisiteProducer : ColonialElementProducer
  incidentWeldProducer : ColonialElementProducer
  proofRelevantElementProducer : ColonialElementProducer
  applicabilityJurisdictionProducer : ColonialElementProducer
  violationProducer : ColonialElementProducer
  liabilityRemedyProducer : ColonialElementProducer


reverseElementNeed : ColonialElementConsumerNeed → ColonialElementProducer
reverseElementNeed needClassificationContent = classificationContentProducer
reverseElementNeed needAuthorityMeaningComparison = authorityMeaningProducer
reverseElementNeed needOperationalPrerequisite = powerPrerequisiteProducer
reverseElementNeed needIncidentSameObjectWeld = incidentWeldProducer
reverseElementNeed needAnalyticalElementProof = proofRelevantElementProducer
reverseElementNeed needWrongTypeApplicability = applicabilityJurisdictionProducer
reverseElementNeed needWrongTypeViolation = violationProducer
reverseElementNeed needWrongTypeLiability = liabilityRemedyProducer

currentHerzogClassificationResidual : Lineage.LineageResidual
currentHerzogClassificationResidual = Lineage.firstLineageResidual
  Lineage.zionistRepertoireReachedClassification
  Lineage.canonicalCurrentLineageCutset

currentHerzogClassificationResidualIsContent :
  currentHerzogClassificationResidual ≡ Lineage.classificationContentResidual
currentHerzogClassificationResidualIsContent = refl

currentWrongTypeApplicabilityRequirement : Wrong.RequiredReceiptKind
currentWrongTypeApplicabilityRequirement = Wrong.requiredReceipt Wrong.needsApplicability

currentWrongTypeViolationRequirement : Wrong.RequiredReceiptKind
currentWrongTypeViolationRequirement = Wrong.requiredReceipt Wrong.needsViolation

currentWrongTypeLiabilityRequirement : Wrong.RequiredReceiptKind
currentWrongTypeLiabilityRequirement = Wrong.requiredReceipt Wrong.needsLiability

------------------------------------------------------------------------
-- Existing colonial owner already states the historical/modern boundary; reuse
-- it rather than inventing a stronger coloniality claim here.
------------------------------------------------------------------------

modernPoliceMotiveStillNotInheritedFromHistory :
  ColonialPrereq.WrongTypePrerequisiteBoundary.historicalConstitutiveMechanismAutomaticallyModernPoliceMotive
    ColonialPrereq.canonicalWrongTypePrerequisiteBoundary ≡ false
modernPoliceMotiveStillNotInheritedFromHistory = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OpenRequirementCountsAsSatisfied : Set where
data AnalyticalElementIsMunicipalWrongElement : Set where
data AnalyticalElementProofAutomaticallyAdmitsWrongType : Set where
data AnalyticalElementProofAutomaticallyCreatesViolation : Set where
data AnalyticalElementProofAutomaticallyCreatesLiability : Set where

openRequirementIsNotPayment : OpenRequirementCountsAsSatisfied → ⊥
openRequirementIsNotPayment ()

analyticalElementDoesNotBecomeMunicipalElement : AnalyticalElementIsMunicipalWrongElement → ⊥
analyticalElementDoesNotBecomeMunicipalElement ()

elementDoesNotAutoAdmitWrongType : AnalyticalElementProofAutomaticallyAdmitsWrongType → ⊥
elementDoesNotAutoAdmitWrongType ()

elementDoesNotAutoViolateWrongType : AnalyticalElementProofAutomaticallyCreatesViolation → ⊥
elementDoesNotAutoViolateWrongType ()

elementDoesNotAutoCreateLiability : AnalyticalElementProofAutomaticallyCreatesLiability → ⊥
elementDoesNotAutoCreateLiability ()

wrongTypeIdStillDoesNotGenerateElements : Elements.WrongTypeIdAloneDeterminesAllElements → ⊥
wrongTypeIdStillDoesNotGenerateElements = Elements.wrongTypeIdDoesNotGenerateElements
