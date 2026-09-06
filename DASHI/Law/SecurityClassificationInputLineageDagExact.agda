module DASHI.Law.SecurityClassificationInputLineageDagExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.SecurityClassificationProvenanceBidiExact as Security
import DASHI.Law.ZionistInstitutionalCarrierGraphBidiExact as Carrier

------------------------------------------------------------------------
-- Classification-input lineage DAG.
-- A threat/risk proposition must travel through named atoms and edges before
-- it may be used to explain an operational classification or field tactic.
------------------------------------------------------------------------

data InputSourceActor : Set where
  nswPoliceIntelligence
  nswPoliceCommand
  protectedPersonSecurity
  federalSecurityAgency
  foreignDiplomaticActor
  israeliSecurityDetail
  privateSecurityLiaison
  politicalExecutive
  mediaNarrative
  sourceUnknown : InputSourceActor

data InputAtomKind : Set where
  threatReport
  intelligenceAssessment
  protectedPersonConcern
  protestPoliticalContent
  crowdBehaviourObservation
  foreignLiaisonStatement
  privateSecurityStatement
  weaponsIntelligence
  counterProtestInformation
  postHocNarrative : InputAtomKind

data LineageStage : Set where
  rawInput
  intelligenceProduct
  riskAssessment
  securityClassification
  operationalOrder
  unitBriefing
  fieldTactic : LineageStage

data LineageClosure : Set where
  stageClosed
  stageOpen
  stageConflict : LineageClosure

record ClassificationInputAtom : Set where
  constructor classificationInputAtom
  field
    sourceActor : InputSourceActor
    atomKind : InputAtomKind
    contentReference : String
    sourceReference : String
    observedBeforeOperation : Bool

open ClassificationInputAtom public

record LineageEdge : Set where
  constructor lineageEdge
  field
    sourceStage : LineageStage
    targetStage : LineageStage
    contentPreserved : Bool
    closure : LineageClosure
    edgeReference : String

open LineageEdge public

record ClassificationLineage : Set where
  constructor classificationLineage
  field
    input : ClassificationInputAtom
    toIntelligence : LineageEdge
    toRiskAssessment : LineageEdge
    toClassification : LineageEdge
    toOperationalOrder : LineageEdge
    toUnitBriefing : LineageEdge
    toFieldTactic : LineageEdge
    lineageReference : String

open ClassificationLineage public

------------------------------------------------------------------------
-- Herzog-shaped current state: public post-hoc characterisations exist, but
-- the pre-event input lineage remains open until underlying records are found.
------------------------------------------------------------------------

herzogPublicNarrativeAtom : ClassificationInputAtom
herzogPublicNarrativeAtom = classificationInputAtom
  nswPoliceCommand postHocNarrative
  "Commissioner post-event aggressive/volatile crowd characterisation"
  "ABC reporting of NSW Police post-event account"
  false

openEdge : LineageStage → LineageStage → String → LineageEdge
openEdge a b ref = lineageEdge a b false stageOpen ref

canonicalHerzogOpenLineage : ClassificationLineage
canonicalHerzogOpenLineage = classificationLineage
  herzogPublicNarrativeAtom
  (openEdge rawInput intelligenceProduct "pre-event intelligence producer not acquired")
  (openEdge intelligenceProduct riskAssessment "risk assessment producer not acquired")
  (openEdge riskAssessment securityClassification "pre-action classification producer not acquired")
  (openEdge securityClassification operationalOrder "classification-to-order link not acquired")
  (openEdge operationalOrder unitBriefing "command transmission/unit briefing not acquired")
  (openEdge unitBriefing fieldTactic "field tactic lineage not fully reconstructed")
  "post-hoc narrative cannot backfill the missing pre-action lineage"

------------------------------------------------------------------------
-- BIDI consumers.
------------------------------------------------------------------------

data LineageClaim : Set where
  foreignInputReachedRiskAssessment
  privateSecurityInputReachedRiskAssessment
  zionistRepertoireReachedClassification
  classificationProducedOperationalOrder
  operationalOrderProducedFieldTactic
  completeThreatLineage : LineageClaim

data LineageProducer : Set where
  foreignInputDocumentProducer
  privateSecurityInputDocumentProducer
  classificationContentAndCarrierProducer
  classificationOrderLinkProducer
  orderFieldTransmissionProducer
  completeLineageProducer : LineageProducer

reverseLineage : LineageClaim → LineageProducer
reverseLineage foreignInputReachedRiskAssessment = foreignInputDocumentProducer
reverseLineage privateSecurityInputReachedRiskAssessment = privateSecurityInputDocumentProducer
reverseLineage zionistRepertoireReachedClassification = classificationContentAndCarrierProducer
reverseLineage classificationProducedOperationalOrder = classificationOrderLinkProducer
reverseLineage operationalOrderProducedFieldTactic = orderFieldTransmissionProducer
reverseLineage completeThreatLineage = completeLineageProducer

record LineageCutset : Set where
  constructor lineageCutset
  field
    foreignInputClosed : Bool
    privateSecurityInputClosed : Bool
    classificationContentClosed : Bool
    carrierContentClosed : Bool
    orderLinkClosed : Bool
    fieldTransmissionClosed : Bool
    cutsetReference : String

open LineageCutset public

data LineageResidual : Set where
  foreignInputResidual
  privateSecurityInputResidual
  classificationContentResidual
  carrierContentResidual
  orderLinkResidual
  fieldTransmissionResidual
  lineageClosed : LineageResidual

firstLineageResidual : LineageClaim → LineageCutset → LineageResidual
firstLineageResidual foreignInputReachedRiskAssessment c with foreignInputClosed c
... | false = foreignInputResidual
... | true = lineageClosed
firstLineageResidual privateSecurityInputReachedRiskAssessment c with privateSecurityInputClosed c
... | false = privateSecurityInputResidual
... | true = lineageClosed
firstLineageResidual zionistRepertoireReachedClassification c with classificationContentClosed c
... | false = classificationContentResidual
... | true with carrierContentClosed c
...   | false = carrierContentResidual
...   | true = lineageClosed
firstLineageResidual classificationProducedOperationalOrder c with orderLinkClosed c
... | false = orderLinkResidual
... | true = lineageClosed
firstLineageResidual operationalOrderProducedFieldTactic c with fieldTransmissionClosed c
... | false = fieldTransmissionResidual
... | true = lineageClosed
firstLineageResidual completeThreatLineage c with classificationContentClosed c
... | false = classificationContentResidual
... | true with orderLinkClosed c
...   | false = orderLinkResidual
...   | true with fieldTransmissionClosed c
...     | false = fieldTransmissionResidual
...     | true = lineageClosed

canonicalCurrentLineageCutset : LineageCutset
canonicalCurrentLineageCutset = lineageCutset
  false false false false false false
  "public network/context exists; pre-action Herzog classification-input lineage remains documentary-open"

currentZionistClassificationClaimStopsAtContent :
  firstLineageResidual zionistRepertoireReachedClassification canonicalCurrentLineageCutset
  ≡ classificationContentResidual
currentZionistClassificationClaimStopsAtContent = refl

------------------------------------------------------------------------
-- Cross-check donor producers.
------------------------------------------------------------------------

foreignClassificationProducer : Security.SecurityClassificationProducer
foreignClassificationProducer = Security.foreignLiaisonProducer

carrierClassificationProducer : Carrier.CarrierProducer
carrierClassificationProducer = Carrier.nswClassificationContentAndForeignLiaisonProducer

record LineageBoundary : Set where
  constructor lineageBoundary
  field
    institutionalNetworkProvesThreatInput : Bool
    institutionalNetworkProvesThreatInputIsFalse : institutionalNetworkProvesThreatInput ≡ false
    foreignPresenceProvesClassificationInfluence : Bool
    foreignPresenceProvesClassificationInfluenceIsFalse : foreignPresenceProvesClassificationInfluence ≡ false
    postHocNarrativeRepairsMissingPreActionLineage : Bool
    postHocNarrativeRepairsMissingPreActionLineageIsFalse : postHocNarrativeRepairsMissingPreActionLineage ≡ false
    classificationSimilarityProvesSharedSource : Bool
    classificationSimilarityProvesSharedSourceIsFalse : classificationSimilarityProvesSharedSource ≡ false

canonicalLineageBoundary : LineageBoundary
canonicalLineageBoundary = lineageBoundary false refl false refl false refl false refl
