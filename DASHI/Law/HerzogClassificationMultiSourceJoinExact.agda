module DASHI.Law.HerzogClassificationMultiSourceJoinExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.DisclosureReadyClassificationInputAtomExact as Atom
import DASHI.Law.IndependentEvidenceProvenanceExact as Independent
import DASHI.Law.EvidenceProvenanceDependencyDagExact as Dag
import DASHI.Law.HerzogIncidentClassificationLineageWeldExact as IncidentWeld
import DASHI.Law.MaboCountrySecurityClassificationCrossPollinationExact as MaboCross

------------------------------------------------------------------------
-- Multi-source join for disclosed threat/classification propositions.
-- Multiple documents may repeat one upstream proposition.  Receipt count,
-- semantic agreement, producer independence, and same-object lineage are
-- therefore independent coordinates.
------------------------------------------------------------------------

data JoinSourceKind : Set where
  policeIntelligenceCopy
  protectedPersonSecurityCopy
  foreignLiaisonCopy
  privateSecurityCopy
  operationalOrderCopy
  unitBriefingCopy
  mediaCopy
  unknownCopy : JoinSourceKind

data JoinRelation : Set where
  directDerivation
  commonUpstreamProducer
  independentProducer
  semanticSimilarityOnly
  relationOpen
  relationConflict : JoinRelation

data JoinClosure : Set where
  joinClosed
  joinOpen
  joinConflict : JoinClosure

record JoinedAtomReceipt : Set where
  constructor joinedAtomReceipt
  field
    atom : Atom.DisclosureInputAtom
    sourceKind : JoinSourceKind
    joinRelation : JoinRelation
    ultimateProducerReference : String
    semanticAgreementClosed : Bool
    independenceClosed : Bool
    joinReference : String

open JoinedAtomReceipt public

record FourDocumentJoin : Set where
  constructor fourDocumentJoin
  field
    first second third fourth : JoinedAtomReceipt
    sameUnderlyingPropositionClosed : Bool
    atLeastTwoIndependentProducersClosed : Bool
    classificationUseClosed : Bool
    incidentUseClosed : Bool
    joinClosure : JoinClosure
    corpusReference : String

open FourDocumentJoin public

------------------------------------------------------------------------
-- Synthetic calibration: four copies can still be one producer.
------------------------------------------------------------------------

syntheticOrigin : Atom.DisclosureInputAtom
syntheticOrigin = Atom.disclosureInputAtom
  "SYNTHETIC-THREAT-ORIGIN"
  Atom.policeIntelligenceDocument
  Atom.Lineage.nswPoliceIntelligence
  "synthetic origin intelligence note"
  "synthetic paragraph 1"
  "synthetic threat proposition"
  "T0" "intelligence unit" "T0"
  Atom.atomSourceBacked
  "calibration only; not a Herzog historical assertion"

syntheticCopy : String → JoinSourceKind → JoinedAtomReceipt
syntheticCopy ident kind = joinedAtomReceipt
  (Atom.disclosureInputAtom ident Atom.operationalBriefing Atom.Lineage.nswPoliceCommand
    "synthetic derivative document" "synthetic location"
    "synthetic threat proposition" "T1" "operations" "T1"
    Atom.atomSourceBacked "calibration derivative")
  kind commonUpstreamProducer
  "SYNTHETIC-THREAT-ORIGIN"
  true false
  "same proposition copied from one upstream origin"

canonicalFourCopiesOneProducer : FourDocumentJoin
canonicalFourCopiesOneProducer = fourDocumentJoin
  (syntheticCopy "COPY-1" policeIntelligenceCopy)
  (syntheticCopy "COPY-2" protectedPersonSecurityCopy)
  (syntheticCopy "COPY-3" foreignLiaisonCopy)
  (syntheticCopy "COPY-4" operationalOrderCopy)
  true false false false joinClosed
  "four documentary surfaces, one ultimate producer: multiplicity does not create independent corroboration"

fourCopiesDoNotCloseIndependence :
  atLeastTwoIndependentProducersClosed canonicalFourCopiesOneProducer ≡ false
fourCopiesDoNotCloseIndependence = refl

------------------------------------------------------------------------
-- Explicit reuse of the generic provenance owners.
------------------------------------------------------------------------

sameContentCannotReconstructIndependence :
  Independent.NF.FactorsThrough Independent.contentProjection Independent.provenanceStrength → ⊥
sameContentCannotReconstructIndependence = Independent.sameContentCannotReconstructIndependence

multipleReceiptsNotAutomaticallyIndependent :
  Dag.multipleReceiptsAutomaticallyIndependent Dag.canonicalProvenanceDagBoundary ≡ false
multipleReceiptsNotAutomaticallyIndependent = refl

sharedProducerIsNotIndependentCorroboration :
  Dag.sharedUltimateProducerCountsAsIndependentCorroboration Dag.canonicalProvenanceDagBoundary ≡ false
sharedProducerIsNotIndependentCorroboration = refl

------------------------------------------------------------------------
-- Current Herzog acquisition state.
------------------------------------------------------------------------

data JoinClaim : Set where
  threatPropositionAppearsInMultipleDocuments
  threatPropositionHasIndependentCorroboration
  foreignAndPoliceDocumentsAreIndependent
  joinedPropositionEnteredClassification
  joinedPropositionReachedSpecificIncident
  countryMeaningAppearsInThreatInput : JoinClaim

data JoinProducer : Set where
  multiDocumentCorpusProducer
  ultimateProducerSeparationProducer
  crossInstitutionIndependenceProducer
  classificationCrossReferenceProducer
  incidentSameObjectJoinProducer
  countryMeaningLiteralAtomProducer : JoinProducer

reverseJoin : JoinClaim → JoinProducer
reverseJoin threatPropositionAppearsInMultipleDocuments = multiDocumentCorpusProducer
reverseJoin threatPropositionHasIndependentCorroboration = ultimateProducerSeparationProducer
reverseJoin foreignAndPoliceDocumentsAreIndependent = crossInstitutionIndependenceProducer
reverseJoin joinedPropositionEnteredClassification = classificationCrossReferenceProducer
reverseJoin joinedPropositionReachedSpecificIncident = incidentSameObjectJoinProducer
reverseJoin countryMeaningAppearsInThreatInput = countryMeaningLiteralAtomProducer

record CurrentJoinCutset : Set where
  constructor currentJoinCutset
  field
    multiDocumentCorpusClosed : Bool
    ultimateProducerSeparationClosed : Bool
    classificationCrossReferenceClosed : Bool
    incidentJoinClosed : Bool
    countryMeaningAtomClosed : Bool
    cutsetReference : String

open CurrentJoinCutset public

data JoinResidual : Set where
  corpusResidual
  independenceResidual
  classificationResidual
  incidentResidual
  countryMeaningResidual
  joinComplete : JoinResidual

firstJoinResidual : JoinClaim → CurrentJoinCutset → JoinResidual
firstJoinResidual threatPropositionAppearsInMultipleDocuments c with multiDocumentCorpusClosed c
... | false = corpusResidual
... | true = joinComplete
firstJoinResidual threatPropositionHasIndependentCorroboration c with multiDocumentCorpusClosed c
... | false = corpusResidual
... | true with ultimateProducerSeparationClosed c
...   | false = independenceResidual
...   | true = joinComplete
firstJoinResidual foreignAndPoliceDocumentsAreIndependent c with ultimateProducerSeparationClosed c
... | false = independenceResidual
... | true = joinComplete
firstJoinResidual joinedPropositionEnteredClassification c with classificationCrossReferenceClosed c
... | false = classificationResidual
... | true = joinComplete
firstJoinResidual joinedPropositionReachedSpecificIncident c with classificationCrossReferenceClosed c
... | false = classificationResidual
... | true with incidentJoinClosed c
...   | false = incidentResidual
...   | true = joinComplete
firstJoinResidual countryMeaningAppearsInThreatInput c with countryMeaningAtomClosed c
... | false = countryMeaningResidual
... | true = joinComplete

canonicalCurrentJoinCutset : CurrentJoinCutset
canonicalCurrentJoinCutset = currentJoinCutset false false false false false
  "Herzog pre-event disclosure corpus not yet acquired at atom granularity"

currentIndependentCorroborationStopsAtCorpus :
  firstJoinResidual threatPropositionHasIndependentCorroboration canonicalCurrentJoinCutset
  ≡ corpusResidual
currentIndependentCorroborationStopsAtCorpus = refl

currentCountryMeaningStopsAtLiteralAtom :
  firstJoinResidual countryMeaningAppearsInThreatInput canonicalCurrentJoinCutset
  ≡ countryMeaningResidual
currentCountryMeaningStopsAtLiteralAtom = refl

------------------------------------------------------------------------
-- Cross-pollination pins.
------------------------------------------------------------------------

prayerIncidentProducer : IncidentWeld.IncidentLineageProducer
prayerIncidentProducer = IncidentWeld.prayerSameObjectWeldProducer

countryClassificationProducer : MaboCross.SecurityCountryProducer
countryClassificationProducer = MaboCross.classificationInputContentProducer

record MultiSourceJoinBoundary : Set where
  constructor multiSourceJoinBoundary
  field
    fourDocumentsMeanFourIndependentSources : Bool
    fourDocumentsMeanFourIndependentSourcesIsFalse : fourDocumentsMeanFourIndependentSources ≡ false
    foreignLetterAndPoliceBriefAreIndependentByInstitutionName : Bool
    foreignLetterAndPoliceBriefAreIndependentByInstitutionNameIsFalse : foreignLetterAndPoliceBriefAreIndependentByInstitutionName ≡ false
    semanticAgreementProvesCommonHistoricalSource : Bool
    semanticAgreementProvesCommonHistoricalSourceIsFalse : semanticAgreementProvesCommonHistoricalSource ≡ false
    repeatedThreatLanguageProvesClassificationCausation : Bool
    repeatedThreatLanguageProvesClassificationCausationIsFalse : repeatedThreatLanguageProvesClassificationCausation ≡ false
    repeatedThreatLanguageProvesIncidentCausation : Bool
    repeatedThreatLanguageProvesIncidentCausationIsFalse : repeatedThreatLanguageProvesIncidentCausation ≡ false
    criticalCountryInterpretationSubstitutesForLiteralInputAtom : Bool
    criticalCountryInterpretationSubstitutesForLiteralInputAtomIsFalse : criticalCountryInterpretationSubstitutesForLiteralInputAtom ≡ false

canonicalMultiSourceJoinBoundary : MultiSourceJoinBoundary
canonicalMultiSourceJoinBoundary =
  multiSourceJoinBoundary false refl false refl false refl false refl false refl false refl
