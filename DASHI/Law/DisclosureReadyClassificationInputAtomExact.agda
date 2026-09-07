module DASHI.Law.DisclosureReadyClassificationInputAtomExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.SecurityClassificationInputLineageDagExact as Lineage

------------------------------------------------------------------------
-- Disclosure-ready source atom.
-- Each paragraph / briefing proposition is retained as a bounded source object,
-- with attribution, time, recipient and semantic-transport status separated.
------------------------------------------------------------------------

data DocumentSourceRole : Set where
  policeIntelligenceDocument : DocumentSourceRole
  operationalBriefing : DocumentSourceRole
  protectedPersonSecurityBrief : DocumentSourceRole
  federalSecurityInput : DocumentSourceRole
  foreignDiplomaticInput : DocumentSourceRole
  israeliSecurityInput : DocumentSourceRole
  privateSecurityInput : DocumentSourceRole
  executiveDirection : DocumentSourceRole
  litigationDisclosure : DocumentSourceRole
  secondaryReport : DocumentSourceRole
  sourceRoleUnknown : DocumentSourceRole

data SemanticTransport : Set where
  exactPreservation : SemanticTransport
  boundedParaphrase : SemanticTransport
  narrowedMeaning : SemanticTransport
  broadenedMeaning : SemanticTransport
  reclassifiedMeaning : SemanticTransport
  semanticConflict : SemanticTransport
  semanticOpen : SemanticTransport

data AtomClosure : Set where
  atomSourceBacked : AtomClosure
  atomDisclosedButUnverified : AtomClosure
  atomReported : AtomClosure
  atomOpen : AtomClosure
  atomConflict : AtomClosure

record DisclosureInputAtom : Set where
  constructor disclosureInputAtom
  field
    atomId : String
    sourceRole : DocumentSourceRole
    sourceActor : Lineage.InputSourceActor
    sourceDocument : String
    sourceLocation : String
    literalOrBoundedContent : String
    createdAt : String
    receivedBy : String
    receivedAt : String
    closure : AtomClosure
    provenanceReference : String

open DisclosureInputAtom public

record AtomTransformation : Set where
  constructor atomTransformation
  field
    sourceAtomId : String
    targetStage : Lineage.LineageStage
    transformedContent : String
    semanticTransport : SemanticTransport
    transformer : String
    transformationReference : String

open AtomTransformation public

------------------------------------------------------------------------
-- Same-object chain receipt.
------------------------------------------------------------------------

record AtomLineageChain : Set where
  constructor atomLineageChain
  field
    sourceAtom : DisclosureInputAtom
    intelligenceTransformation : AtomTransformation
    riskTransformation : AtomTransformation
    classificationTransformation : AtomTransformation
    orderTransformation : AtomTransformation
    briefingTransformation : AtomTransformation
    fieldTransformation : AtomTransformation
    sameObjectChainClosed : Bool
    sameObjectReference : String

open AtomLineageChain public

------------------------------------------------------------------------
-- Current Herzog disclosure fixture: schema is ready, content is not invented.
------------------------------------------------------------------------

herzogPreEventInputPlaceholder : DisclosureInputAtom
herzogPreEventInputPlaceholder = disclosureInputAtom
  "HERZOG-PRE-EVENT-INPUT-UNACQUIRED"
  sourceRoleUnknown
  Lineage.sourceUnknown
  "pre-event briefing/intelligence document not yet acquired"
  "unknown"
  "content not supplied"
  "unknown"
  "unknown"
  "unknown"
  atomOpen
  "placeholder only; no historical proposition promoted"

openTransformation : String → Lineage.LineageStage → AtomTransformation
openTransformation atom stage = atomTransformation
  atom stage "content unresolved" semanticOpen "unknown" "producer not acquired"

canonicalOpenHerzogAtomChain : AtomLineageChain
canonicalOpenHerzogAtomChain = atomLineageChain
  herzogPreEventInputPlaceholder
  (openTransformation "HERZOG-PRE-EVENT-INPUT-UNACQUIRED" Lineage.intelligenceProduct)
  (openTransformation "HERZOG-PRE-EVENT-INPUT-UNACQUIRED" Lineage.riskAssessment)
  (openTransformation "HERZOG-PRE-EVENT-INPUT-UNACQUIRED" Lineage.securityClassification)
  (openTransformation "HERZOG-PRE-EVENT-INPUT-UNACQUIRED" Lineage.operationalOrder)
  (openTransformation "HERZOG-PRE-EVENT-INPUT-UNACQUIRED" Lineage.unitBriefing)
  (openTransformation "HERZOG-PRE-EVENT-INPUT-UNACQUIRED" Lineage.fieldTactic)
  false
  "same-object lineage intentionally open until disclosed material supplies exact atoms and transformations"

------------------------------------------------------------------------
-- BIDI consumer routing.
------------------------------------------------------------------------

data AtomClaim : Set where
  sourceActorKnown : AtomClaim
  literalThreatPropositionKnown : AtomClaim
  atomEnteredRiskAssessment : AtomClaim
  meaningPreservedIntoClassification : AtomClaim
  atomEnteredOperationalOrder : AtomClaim
  atomReachedFieldUnit : AtomClaim
  atomCausedFieldTactic : AtomClaim

data AtomProducer : Set where
  sourceDocumentProducer : AtomProducer
  literalContentProducer : AtomProducer
  riskAssessmentCrossReferenceProducer : AtomProducer
  semanticTransportProducer : AtomProducer
  operationalOrderCrossReferenceProducer : AtomProducer
  unitBriefingReceiptProducer : AtomProducer
  incidentCausalWeldProducer : AtomProducer

reverseAtom : AtomClaim → AtomProducer
reverseAtom sourceActorKnown = sourceDocumentProducer
reverseAtom literalThreatPropositionKnown = literalContentProducer
reverseAtom atomEnteredRiskAssessment = riskAssessmentCrossReferenceProducer
reverseAtom meaningPreservedIntoClassification = semanticTransportProducer
reverseAtom atomEnteredOperationalOrder = operationalOrderCrossReferenceProducer
reverseAtom atomReachedFieldUnit = unitBriefingReceiptProducer
reverseAtom atomCausedFieldTactic = incidentCausalWeldProducer

record DisclosureAtomBoundary : Set where
  constructor disclosureAtomBoundary
  field
    documentPresenceProvesMeaningPreserved : Bool
    documentPresenceProvesMeaningPreservedIsFalse : documentPresenceProvesMeaningPreserved ≡ false
    similarWordsProveSameObjectLineage : Bool
    similarWordsProveSameObjectLineageIsFalse : similarWordsProveSameObjectLineage ≡ false
    disclosedBriefingProvesFieldReceipt : Bool
    disclosedBriefingProvesFieldReceiptIsFalse : disclosedBriefingProvesFieldReceipt ≡ false
    fieldReceiptProvesCausalForceDecision : Bool
    fieldReceiptProvesCausalForceDecisionIsFalse : fieldReceiptProvesCausalForceDecision ≡ false
    missingDocumentMeansNoInputExisted : Bool
    missingDocumentMeansNoInputExistedIsFalse : missingDocumentMeansNoInputExisted ≡ false

canonicalDisclosureAtomBoundary : DisclosureAtomBoundary
canonicalDisclosureAtomBoundary =
  disclosureAtomBoundary false refl false refl false refl false refl false refl
