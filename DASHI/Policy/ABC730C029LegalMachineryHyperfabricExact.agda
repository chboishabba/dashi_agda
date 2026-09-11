module DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.QueryFactorisationSufficiency as QFS
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Admissible
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Hyper
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Law.DisclosureReadyClassificationInputAtomExact as Atom
import DASHI.Law.MaboCountrySecurityClassificationCrossPollinationExact as Mabo
import DASHI.Policy.ABC730C029EvidenceRoadmapExact as Roadmap
import DASHI.Policy.ABC730C029IbrahimSourceAtlasExact as Atlas
import DASHI.Policy.ABC730AustralianOriginBaselineExact as Origin
import DASHI.Policy.ABC730AustralianAdviceAcquisitionSnowballExact as Advice
import DASHI.Policy.ABC730FirmDestinationExposureSnowballExact as Firm
import DASHI.Policy.ABC730PalestinianIncidenceSnowballExact as Palestinian
import DASHI.Policy.ABC730SettlementTradeMeasurementGapExact as Measurement

------------------------------------------------------------------------
-- Purpose
--
-- Thin cross-pollination of the existing C029 lane with the repository's
-- legal/representation machinery.  This owner adds no new source authority.
-- It makes explicit why several already-acquired objects are valid objects but
-- the wrong type for particular consumers, why coarse administrative surfaces
-- cannot answer situated policy questions, and which hard gates must be paid
-- before cost/effect comparison or evaluative promotion is admissible.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Mabo / intersectionality: coarse administrative charts can erase exactly
-- the distinction the downstream legal/policy consumer needs.
------------------------------------------------------------------------

data IsraeliOriginSituated : Set where
  greenLineIsraeliOrigin : IsraeliOriginSituated
  settlementOrigin : IsraeliOriginSituated

data CountryOriginSurface : Set where
  israelCountryOrigin : CountryOriginSurface

data SettlementRestrictionOutcome : Set where
  outsideSettlementRestriction : SettlementRestrictionOutcome
  insideSettlementRestriction : SettlementRestrictionOutcome

countryOriginObserver : IsraeliOriginSituated → CountryOriginSurface
countryOriginObserver greenLineIsraeliOrigin = israelCountryOrigin
countryOriginObserver settlementOrigin = israelCountryOrigin

settlementRestrictionOutcome : IsraeliOriginSituated → SettlementRestrictionOutcome
settlementRestrictionOutcome greenLineIsraeliOrigin = outsideSettlementRestriction
settlementRestrictionOutcome settlementOrigin = insideSettlementRestriction

settlementOutcomeDiffers :
  settlementRestrictionOutcome greenLineIsraeliOrigin ≡
  settlementRestrictionOutcome settlementOrigin → ⊥
settlementOutcomeDiffers ()

countryOriginErasesSettlementWitness :
  INF.NonFactorabilityWitness countryOriginObserver settlementRestrictionOutcome
countryOriginErasesSettlementWitness = INF.nonFactorabilityWitness
  greenLineIsraeliOrigin settlementOrigin refl settlementOutcomeDiffers

countryOriginCannotDetermineSettlementRestriction :
  INF.FactorsThrough countryOriginObserver settlementRestrictionOutcome → ⊥
countryOriginCannotDetermineSettlementRestriction =
  INF.witnessRulesOutEveryFlatFactorisation countryOriginErasesSettlementWitness

------------------------------------------------------------------------
-- Affected-class flattening has the same problem. "Palestinian" does not
-- determine policy incidence when situated economic roles differ.
------------------------------------------------------------------------

data PalestinianSituatedRole : Set where
  settlementDependentWorker : PalestinianSituatedRole
  substitutingPalestinianProducer : PalestinianSituatedRole

data PalestinianFlatLabel : Set where
  palestinianAffectedClass : PalestinianFlatLabel

data PalestinianIncidenceOutcome : Set where
  exposedEmploymentLossChannel : PalestinianIncidenceOutcome
  possibleProducerSubstitutionGainChannel : PalestinianIncidenceOutcome

palestinianClassObserver : PalestinianSituatedRole → PalestinianFlatLabel
palestinianClassObserver settlementDependentWorker = palestinianAffectedClass
palestinianClassObserver substitutingPalestinianProducer = palestinianAffectedClass

palestinianIncidenceOutcome : PalestinianSituatedRole → PalestinianIncidenceOutcome
palestinianIncidenceOutcome settlementDependentWorker = exposedEmploymentLossChannel
palestinianIncidenceOutcome substitutingPalestinianProducer = possibleProducerSubstitutionGainChannel

palestinianOutcomesDiffer :
  palestinianIncidenceOutcome settlementDependentWorker ≡
  palestinianIncidenceOutcome substitutingPalestinianProducer → ⊥
palestinianOutcomesDiffer ()

palestinianClassErasesIncidenceWitness :
  INF.NonFactorabilityWitness palestinianClassObserver palestinianIncidenceOutcome
palestinianClassErasesIncidenceWitness = INF.nonFactorabilityWitness
  settlementDependentWorker substitutingPalestinianProducer refl palestinianOutcomesDiffer

palestinianLabelCannotDetermineNetIncidence :
  INF.FactorsThrough palestinianClassObserver palestinianIncidenceOutcome → ⊥
palestinianLabelCannotDetermineNetIncidence =
  INF.witnessRulesOutEveryFlatFactorisation palestinianClassErasesIncidenceWitness

------------------------------------------------------------------------
-- 2. FactorsThrough / consumer sufficiency: a surface can be useful for one
-- query and still fail another. Country-level origin remains useful; it is not
-- settlement-origin sufficient.
------------------------------------------------------------------------

data OriginQuery : Set where
  countryIdentityQuery : OriginQuery
  settlementApplicabilityQuery : OriginQuery

data OriginAnswer : Set where
  israelAnswer : OriginAnswer
  outsideAnswer : OriginAnswer
  insideAnswer : OriginAnswer

originQuestions : QFS.InquiryQuestionFamily IsraeliOriginSituated OriginQuery
originQuestions = QFS.inquiryQuestionFamily (λ _ → OriginAnswer) ask
  where
    ask : (q : OriginQuery) → IsraeliOriginSituated → OriginAnswer
    ask countryIdentityQuery greenLineIsraeliOrigin = israelAnswer
    ask countryIdentityQuery settlementOrigin = israelAnswer
    ask settlementApplicabilityQuery greenLineIsraeliOrigin = outsideAnswer
    ask settlementApplicabilityQuery settlementOrigin = insideAnswer

countryIdentityFactors :
  QFS.FactorsThrough originQuestions countryOriginObserver countryIdentityQuery
countryIdentityFactors = QFS.factorsThrough quotient proof
  where
    quotient : CountryOriginSurface → OriginAnswer
    quotient israelCountryOrigin = israelAnswer

    proof :
      (s : IsraeliOriginSituated) →
      QFS.ask originQuestions countryIdentityQuery s ≡ quotient (countryOriginObserver s)
    proof greenLineIsraeliOrigin = refl
    proof settlementOrigin = refl

------------------------------------------------------------------------
-- 3. WrongType: valid evidence objects offered to the wrong indexed obligation.
-- This is an adapter to the repo's WrongType discipline, not a new global
-- WrongType ontology.
------------------------------------------------------------------------

data C029EvidenceObject : Set where
  ministerialRationaleStatement : C029EvidenceObject
  totalIsraelTradeAggregate : C029EvidenceObject
  ohchrSettlementBusinessList : C029EvidenceObject
  pcbsSettlementWorkerCount : C029EvidenceObject
  australianCountryOriginCapability : C029EvidenceObject
  verifiedEntityQid : C029EvidenceObject

data C029ConsumerObligation : Set where
  publicRationaleWording : C029ConsumerObligation
  settlementTradeMagnitude : C029ConsumerObligation
  currentDestinationExporterSet : C029ConsumerObligation
  palestinianNetIncidence : C029ConsumerObligation
  settlementSubcountryClassifier : C029ConsumerObligation
  externalEntityIdentity : C029ConsumerObligation

record C029WrongTypeReceipt : Set where
  constructor c029WrongTypeReceipt
  field
    candidate : C029EvidenceObject
    offeredTo : C029ConsumerObligation
    candidateIsValidEvidenceObject : Bool
    satisfiesThisObligation : Bool
    residual : String

open C029WrongTypeReceipt public

ministerialStatementWrongForImpact : C029WrongTypeReceipt
ministerialStatementWrongForImpact = c029WrongTypeReceipt
  ministerialRationaleStatement palestinianNetIncidence true false
  "Primary for the stated rationale, but wrong type for a causal/net-incidence consumer."

totalTradeWrongForSettlementMagnitude : C029WrongTypeReceipt
totalTradeWrongForSettlementMagnitude = c029WrongTypeReceipt
  totalIsraelTradeAggregate settlementTradeMagnitude true false
  "Country-level bilateral trade is valid aggregate evidence but the wrong type for settlement-specific exposure."

businessListWrongForExporterRegister : C029WrongTypeReceipt
businessListWrongForExporterRegister = c029WrongTypeReceipt
  ohchrSettlementBusinessList currentDestinationExporterSet true false
  "Settlement-related business inclusion is not a current UK/Australia destination exporter receipt."

workerCountWrongForNetEffect : C029WrongTypeReceipt
workerCountWrongForNetEffect = c029WrongTypeReceipt
  pcbsSettlementWorkerCount palestinianNetIncidence true false
  "Employment exposure is real but does not determine displacement, substitution, household effect or net policy sign."

countryOriginWrongForSettlementClassifier : C029WrongTypeReceipt
countryOriginWrongForSettlementClassifier = c029WrongTypeReceipt
  australianCountryOriginCapability settlementSubcountryClassifier true false
  "Country-origin infrastructure is a baseline capability, not a settlement-place legal classifier."

qidRightOnlyForIdentity : C029WrongTypeReceipt
qidRightOnlyForIdentity = c029WrongTypeReceipt
  verifiedEntityQid externalEntityIdentity true true
  "QID can pay the external identity coordinate when same-entity resolution is paid; it still does not import proposition truth."

wrongTypeTopologyAnchor : String
wrongTypeTopologyAnchor =
  "DASHI.Interop.SensibLawOntologyTopology: interpretations are indexed by system/perspective/evidence and claims are not world records"

------------------------------------------------------------------------
-- 4. Atom / lineage: the missing Australian advice object must be atomised and
-- welded through the actual decision chain. Similar wording is insufficient.
------------------------------------------------------------------------

data PolicyAdviceStage : Set where
  departmentalAnalysis : PolicyAdviceStage
  ministerialBrief : PolicyAdviceStage
  publicRationale : PolicyAdviceStage
  policyDecision : PolicyAdviceStage

record PolicyAdviceAtom : Set where
  constructor policyAdviceAtom
  field
    atomId : String
    sourceDocument : String
    exactLocator : String
    boundedContent : String
    createdAt : String
    closure : Atom.AtomClosure
    sourceReference : String

open PolicyAdviceAtom public

record PolicyAdviceTransport : Set where
  constructor policyAdviceTransport
  field
    sourceAtomId : String
    fromStage : PolicyAdviceStage
    toStage : PolicyAdviceStage
    transport : Atom.SemanticTransport
    transformationReference : String

open PolicyAdviceTransport public

record C029AdviceLineage : Set where
  constructor c029AdviceLineage
  field
    adviceAtom : PolicyAdviceAtom
    toMinisterialBrief : PolicyAdviceTransport
    toPublicRationale : PolicyAdviceTransport
    toDecision : PolicyAdviceTransport
    sameObjectLineageClosed : Bool
    sameObjectReference : String

open C029AdviceLineage public

openAdviceAtom : PolicyAdviceAtom
openAdviceAtom = policyAdviceAtom
  "C029-AU-ADVICE-ATOM-UNACQUIRED"
  "DFAT/ABF/Treasury/Attorney-General implementation or impact advice not yet acquired"
  "unknown"
  "mechanism, materiality and counterfactual content unresolved"
  "unknown"
  Atom.atomOpen
  "ABC730AustralianAdviceAcquisitionSnowballExact"

openAdviceTransport : PolicyAdviceStage → PolicyAdviceStage → PolicyAdviceTransport
openAdviceTransport from to = policyAdviceTransport
  "C029-AU-ADVICE-ATOM-UNACQUIRED" from to Atom.semanticOpen
  "same-object transformation producer not acquired"

canonicalOpenAdviceLineage : C029AdviceLineage
canonicalOpenAdviceLineage = c029AdviceLineage
  openAdviceAtom
  (openAdviceTransport departmentalAnalysis ministerialBrief)
  (openAdviceTransport ministerialBrief publicRationale)
  (openAdviceTransport publicRationale policyDecision)
  false
  "public rationale cannot backfill the missing advice->brief->decision lineage"

------------------------------------------------------------------------
-- 5. Woogaroo-style cutset: authority, application, incidence and realised
-- outcome are distinct gates.  The shortest residual is explicit.
------------------------------------------------------------------------

data C029CutsetResidual : Set where
  settlementClassifierResidual : C029CutsetResidual
  adviceLineageResidual : C029CutsetResidual
  businessMaterialityResidual : C029CutsetResidual
  palestinianIncidenceResidual : C029CutsetResidual
  israeliIncidenceResidual : C029CutsetResidual
  comparativeCounterfactualResidual : C029CutsetResidual
  c029CutsetClosed : C029CutsetResidual

record C029LegalEvidenceCutset : Set where
  constructor c029LegalEvidenceCutset
  field
    sourceAndRationalePaid : Bool
    australianOriginBaselinePaid : Bool
    settlementClassifierPaid : Bool
    adviceLineagePaid : Bool
    australianBusinessMaterialityPaid : Bool
    palestinianNetIncidencePaid : Bool
    israeliNetIncidencePaid : Bool
    comparativeCounterfactualPaid : Bool
    cutsetReference : String

open C029LegalEvidenceCutset public

firstC029Residual : C029LegalEvidenceCutset → C029CutsetResidual
firstC029Residual c with settlementClassifierPaid c
... | false = settlementClassifierResidual
... | true with adviceLineagePaid c
...   | false = adviceLineageResidual
...   | true with australianBusinessMaterialityPaid c
...     | false = businessMaterialityResidual
...     | true with palestinianNetIncidencePaid c
...       | false = palestinianIncidenceResidual
...       | true with israeliNetIncidencePaid c
...         | false = israeliIncidenceResidual
...         | true with comparativeCounterfactualPaid c
...           | false = comparativeCounterfactualResidual
...           | true = c029CutsetClosed

canonicalC029Cutset : C029LegalEvidenceCutset
canonicalC029Cutset = c029LegalEvidenceCutset
  true true false false false false false false
  "Woogaroo-style source/application/outcome gate decomposition over the C029 policy-evidence consumer"

currentFirstResidualIsSettlementClassifier :
  firstC029Residual canonicalC029Cutset ≡ settlementClassifierResidual
currentFirstResidualIsSettlementClassifier = refl

------------------------------------------------------------------------
-- 6. Admissible transitions: a downstream evaluative move is disabled, not
-- merely assigned low confidence, until prerequisite evidence states exist.
------------------------------------------------------------------------

data C029EvidenceState : Set where
  originBaselineState : C029EvidenceState
  settlementClassifierState : C029EvidenceState
  incidenceEvidenceState : C029EvidenceState
  comparativeEvidenceState : C029EvidenceState
  evaluativeReadyState : C029EvidenceState

data C029Move : Set where
  specifySettlementClassifier : C029Move
  payIncidenceEvidence : C029Move
  comparePolicyInstruments : C029Move
  evaluateAptness : C029Move

data C029Parameter : Set where
  c029Current : C029Parameter

C029Enabled : C029Move → C029Parameter → C029EvidenceState → Set
C029Enabled specifySettlementClassifier c029Current originBaselineState = ⊤
C029Enabled payIncidenceEvidence c029Current settlementClassifierState = ⊤
C029Enabled comparePolicyInstruments c029Current incidenceEvidenceState = ⊤
C029Enabled evaluateAptness c029Current comparativeEvidenceState = ⊤
C029Enabled _ _ _ = ⊥

C029Step : C029Move → C029Parameter → C029EvidenceState → C029EvidenceState
C029Step specifySettlementClassifier _ _ = settlementClassifierState
C029Step payIncidenceEvidence _ _ = incidenceEvidenceState
C029Step comparePolicyInstruments _ _ = comparativeEvidenceState
C029Step evaluateAptness _ _ = evaluativeReadyState

C029Invariant : C029EvidenceState → Set
C029Invariant _ = ⊤

C029Preserves :
  (move : C029Move) →
  (parameter : C029Parameter) →
  (state : C029EvidenceState) →
  C029Enabled move parameter state →
  C029Invariant state →
  C029Invariant (C029Step move parameter state)
C029Preserves _ _ _ _ _ = tt

c029AdmissibleTransitionSystem : Admissible.AdmissibleTransitionSystem
c029AdmissibleTransitionSystem = Admissible.admissibleTransitionSystem
  C029EvidenceState C029Parameter C029Move
  C029Enabled C029Step C029Invariant C029Preserves
  "C029 evidence payment order: origin baseline -> settlement classifier -> incidence -> comparative instrument evidence -> evaluative aptness"

------------------------------------------------------------------------
-- 7. Fibre / hyperfabric: representations are judged against the exact
-- consumer. A compact country-only surface is neither admissible nor adequate
-- for the full C029 comparison merely because it is easy to describe.
------------------------------------------------------------------------

data C029Representation : Set where
  countryOnlyRepresentation : C029Representation
  settlementOriginRepresentation : C029Representation
  settlementOriginIncidenceRepresentation : C029Representation
  fullCounterfactualRepresentation : C029Representation

data C029AdmissibleRepresentation : C029Representation → Set where
  settlementOriginAdmissible : C029AdmissibleRepresentation settlementOriginRepresentation
  settlementOriginIncidenceAdmissible : C029AdmissibleRepresentation settlementOriginIncidenceRepresentation
  fullCounterfactualAdmissible : C029AdmissibleRepresentation fullCounterfactualRepresentation

data C029ConsumerAdequate : C029Representation → Set where
  fullCounterfactualAdequate : C029ConsumerAdequate fullCounterfactualRepresentation

data C029Refines : C029Representation → C029Representation → Set where
  countryToSettlement : C029Refines countryOnlyRepresentation settlementOriginRepresentation
  settlementToIncidence : C029Refines settlementOriginRepresentation settlementOriginIncidenceRepresentation
  incidenceToCounterfactual : C029Refines settlementOriginIncidenceRepresentation fullCounterfactualRepresentation

c029DescriptionLength : C029Representation → Nat
c029DescriptionLength countryOnlyRepresentation = 1
c029DescriptionLength settlementOriginRepresentation = 2
c029DescriptionLength settlementOriginIncidenceRepresentation = 3
c029DescriptionLength fullCounterfactualRepresentation = 4

c029RepresentationReference : C029Representation → String
c029RepresentationReference countryOnlyRepresentation = "country-level origin only"
c029RepresentationReference settlementOriginRepresentation = "settlement-place origin distinguished"
c029RepresentationReference settlementOriginIncidenceRepresentation = "settlement origin plus situated incidence"
c029RepresentationReference fullCounterfactualRepresentation = "origin + incidence + comparative targeted-vs-broad counterfactual"

c029ConsumerProblem : Hyper.ConsumerMDLProblem
c029ConsumerProblem = Hyper.consumerMDLProblem
  C029Representation
  C029AdmissibleRepresentation
  C029ConsumerAdequate
  c029DescriptionLength
  C029Refines
  c029RepresentationReference
  "illustrative structural description length; ranking is downstream of admissibility/adequacy"
  "C029 unintended-consequence / comparative-instrument consumer"

countryOnlyInadequate : C029ConsumerAdequate countryOnlyRepresentation → ⊥
countryOnlyInadequate ()

countryOnlyCounterexample :
  Hyper.ConsumerCounterexample c029ConsumerProblem countryOnlyRepresentation
countryOnlyCounterexample = Hyper.consumerCounterexample
  ⊤ tt countryOnlyInadequate
  "country-level origin erases green-line vs settlement origin and therefore cannot answer settlement-ban applicability"
  "countryOriginErasesSettlementWitness"

------------------------------------------------------------------------
-- 8. Explicit cross-domain boundaries.
------------------------------------------------------------------------

data CountryOriginCapabilityProvesSettlementClassifier : Set where
countryOriginCapabilityDoesNotProveSettlementClassifier :
  CountryOriginCapabilityProvesSettlementClassifier → ⊥
countryOriginCapabilityDoesNotProveSettlementClassifier ()

data AffectedClassNameProvesSituatedIncidence : Set where
affectedClassNameDoesNotProveSituatedIncidence :
  AffectedClassNameProvesSituatedIncidence → ⊥
affectedClassNameDoesNotProveSituatedIncidence ()

data PublicRationaleRepairsMissingAdviceLineage : Set where
publicRationaleDoesNotRepairMissingAdviceLineage :
  PublicRationaleRepairsMissingAdviceLineage → ⊥
publicRationaleDoesNotRepairMissingAdviceLineage ()

data LegalAuthorityProvesRealisedEffect : Set where
legalAuthorityDoesNotProveRealisedEffect : LegalAuthorityProvesRealisedEffect → ⊥
legalAuthorityDoesNotProveRealisedEffect ()

data AdjacencyCreatesSameObjectWeld : Set where
adjacencyDoesNotCreateSameObjectWeld : AdjacencyCreatesSameObjectWeld → ⊥
adjacencyDoesNotCreateSameObjectWeld ()

data CheapRepresentationMayBypassAdmissibility : Set where
cheapRepresentationCannotBypassAdmissibility : CheapRepresentationMayBypassAdmissibility → ⊥
cheapRepresentationCannotBypassAdmissibility ()

------------------------------------------------------------------------
-- Donor anchors: these guarantee this owner is cross-pollination/composition,
-- not a replacement for the authoritative generic machinery.
------------------------------------------------------------------------

intersectionalAnchor : INF.NonFactorabilityWitness countryOriginObserver settlementRestrictionOutcome
intersectionalAnchor = countryOriginErasesSettlementWitness

admissibleBoundaryAnchor : Admissible.AdmissibleTransitionBoundary
admissibleBoundaryAnchor = Admissible.canonicalAdmissibleTransitionBoundary

hyperfabricBoundaryAnchor : Hyper.AdmissibleConsumerMDLBoundary
hyperfabricBoundaryAnchor = Hyper.canonicalAdmissibleConsumerMDLBoundary

atomBoundaryAnchor : Atom.DisclosureAtomBoundary
atomBoundaryAnchor = Atom.canonicalDisclosureAtomBoundary

maboBoundaryAnchor : Mabo.SecurityCountryBoundary
maboBoundaryAnchor = Mabo.canonicalSecurityCountryBoundary

roadmapAnchor : Roadmap.C029RoadmapSummary
roadmapAnchor = Roadmap.canonicalC029RoadmapSummary

atlasAnchor : Atlas.AtlasBoundary
atlasAnchor = Atlas.canonicalAtlasBoundary

originAnchor : Origin.AustralianOriginCapabilityState
originAnchor = Origin.canonicalAustralianOriginCapabilityState

adviceAnchor : Advice.AustralianAdviceAcquisitionFrontier
adviceAnchor = Advice.canonicalAustralianAdviceAcquisitionFrontier

firmAnchor : Firm.FirmDestinationWorkerState
firmAnchor = Firm.canonicalFirmDestinationWorkerState

palestinianAnchor : Palestinian.PalestinianConsequenceState
palestinianAnchor = Palestinian.canonicalPalestinianConsequenceState

measurementAnchor : Measurement.SettlementTradeMeasurementState
measurementAnchor = Measurement.canonicalSettlementTradeMeasurementState

wrongTypeOntologyReference : String
wrongTypeOntologyReference = "DASHI.Interop.SensibLawOntologyTopology.WrongTypeInterpretation"
