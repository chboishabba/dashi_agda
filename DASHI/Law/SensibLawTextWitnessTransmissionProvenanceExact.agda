module DASHI.Law.SensibLawTextWitnessTransmissionProvenanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- TEXT-WITNESS TRANSMISSION PROVENANCE
--
-- Legal and historical text often reaches a parser through several human and
-- institutional observation/transcription/publication stages. Repetition is
-- useful provenance and comparison structure; it is not permission to collapse
-- every witness into a single unqualified truth carrier.
------------------------------------------------------------------------

data WitnessStageKind : Set where
  originalUtteranceOrAct
  judicialDraftOrReasons
  courtReporterObservation
  courtroomNote
  legalRepresentativeNote
  registryOrAdministrativeTranscript
  typistOrPublisherTranscription
  authorisedReportPublication
  unofficialReportPublication
  digitisationStage
  ocrStage
  canonicalTextAdaptation
  parserObservationStage
  : WitnessStageKind

record TextWitnessStage : Set where
  constructor textWitnessStage
  field
    stageReference : String
    stageKind : WitnessStageKind
    actorOrInstitutionReference : String
    inputWitnessReference : String
    outputWitnessReference : String
    temporalReference : String
    transformationReference : String
    provenanceReference : String

open TextWitnessStage public

record TextWitnessLineage : Set₁ where
  constructor textWitnessLineage
  field
    sourceIdentityReference : String
    stages : List TextWitnessStage
    canonicalTextReference : String
    independentlyObservedWitnessReferences : List String
    lineageReference : String

open TextWitnessLineage public

data WitnessRelation : Set where
  sameSourceDifferentTranscription
  sameEventIndependentObservation
  derivativePublication
  quotedDerivative
  uncertainWitnessRelation
  : WitnessRelation

record WitnessComparison : Set where
  constructor witnessComparison
  field
    leftWitnessReference : String
    rightWitnessReference : String
    relation : WitnessRelation
    agreementReference : String
    disagreementReference : String
    independenceReceipt : Set
    comparisonReference : String

open WitnessComparison public

record ParserWitnessReceipt : Set₁ where
  constructor parserWitnessReceipt
  field
    lineage : TextWitnessLineage
    parserObservationReference : String
    exactCanonicalTextReceipt : Set
    parserIsLastObservationStageOnly : Bool
    parserIsLastObservationStageOnlyIsTrue : parserIsLastObservationStageOnly ≡ true
    receiptReference : String

open ParserWitnessReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MultipleTranscriptionsAutomaticallyTruth : Set where
data RepetitionAutomaticallyIndependentCorroboration : Set where
data AuthorisedPublicationAutomaticallyUniversalTruth : Set where
data OCRAutomaticallyAuthoritativeTranscription : Set where
data ParserMayDiscardWitnessLineage : Set where

multipleTranscriptionsDoNotCreateTruth : MultipleTranscriptionsAutomaticallyTruth → ⊥
multipleTranscriptionsDoNotCreateTruth ()

repetitionDoesNotCreateIndependence : RepetitionAutomaticallyIndependentCorroboration → ⊥
repetitionDoesNotCreateIndependence ()

authorisedPublicationDoesNotCreateUniversalTruth :
  AuthorisedPublicationAutomaticallyUniversalTruth → ⊥
authorisedPublicationDoesNotCreateUniversalTruth ()

ocrDoesNotBecomeAuthoritativeTranscription : OCRAutomaticallyAuthoritativeTranscription → ⊥
ocrDoesNotBecomeAuthoritativeTranscription ()

parserMustRetainWitnessLineage : ParserMayDiscardWitnessLineage → ⊥
parserMustRetainWitnessLineage ()

record TextWitnessBoundary : Set where
  constructor textWitnessBoundary
  field
    multipleTransmissionStagesMayBeRetained : Bool
    multipleTransmissionStagesMayBeRetainedIsTrue :
      multipleTransmissionStagesMayBeRetained ≡ true
    independentWitnessesMayBeCompared : Bool
    independentWitnessesMayBeComparedIsTrue : independentWitnessesMayBeCompared ≡ true
    repeatedTextAutomaticallyMeansIndependentEvidence : Bool
    repeatedTextAutomaticallyMeansIndependentEvidenceIsFalse :
      repeatedTextAutomaticallyMeansIndependentEvidence ≡ false
    parserMayEraseTransmissionHistory : Bool
    parserMayEraseTransmissionHistoryIsFalse : parserMayEraseTransmissionHistory ≡ false

canonicalTextWitnessBoundary : TextWitnessBoundary
canonicalTextWitnessBoundary =
  textWitnessBoundary true refl true refl false refl false refl
