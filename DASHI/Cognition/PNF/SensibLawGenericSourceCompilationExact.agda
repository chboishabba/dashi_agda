module DASHI.Cognition.PNF.SensibLawGenericSourceCompilationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- INGEST-1 generic source compilation.
--
-- Source-family structure may differ, but semantic admission begins at the
-- same exact source revision/span membrane.  This owner deliberately separates
-- producer-specific capture from source identity, semantic interpretation and
-- operational observation.
------------------------------------------------------------------------

data SourceFamily : Set where
  document mail chat socialMessage transcript audio imageOCR web wiki :
    SourceFamily
  legalAuthority noteResearch fieldCapture calendar financialRecord :
    SourceFamily
  structuredDataset machineArtifact : SourceFamily

data IngestRoleClass : Set where
  contentSource observerSource operationalSource externalAuthoritySource :
    IngestRoleClass
  contextOverlay : IngestRoleClass

data MailBodySegmentKind : Set where
  authoredHere quotedPriorMessage forwardedMessage signature headerReplica :
    MailBodySegmentKind
  disclaimer attachmentText unknown : MailBodySegmentKind

record GenericSourceCompilationBoundary : Set where
  constructor generic-source-compilation-boundary
  field
    providerSpecificStructurePreserved : Bool
    providerSpecificStructurePreservedIsTrue :
      providerSpecificStructurePreserved ≡ true

    oneCanonicalRevisionSpanABI : Bool
    oneCanonicalRevisionSpanABIIsTrue :
      oneCanonicalRevisionSpanABI ≡ true

    contentSourceMayEnterM12 : Bool
    contentSourceMayEnterM12IsTrue :
      contentSourceMayEnterM12 ≡ true

    externalAuthorityMayEnterM12 : Bool
    externalAuthorityMayEnterM12IsTrue :
      externalAuthorityMayEnterM12 ≡ true

    observerMetadataAutomaticallyBecomesStatement : Bool
    observerMetadataAutomaticallyBecomesStatementIsFalse :
      observerMetadataAutomaticallyBecomesStatement ≡ false

    operationalMetadataAutomaticallyBecomesStatement : Bool
    operationalMetadataAutomaticallyBecomesStatementIsFalse :
      operationalMetadataAutomaticallyBecomesStatement ≡ false

    contextOverlayAutomaticallyBecomesStatement : Bool
    contextOverlayAutomaticallyBecomesStatementIsFalse :
      contextOverlayAutomaticallyBecomesStatement ≡ false

    quotedMailCountsAsIndependentAuthorship : Bool
    quotedMailCountsAsIndependentAuthorshipIsFalse :
      quotedMailCountsAsIndependentAuthorship ≡ false

    forwardedMailCountsAsIndependentAuthorship : Bool
    forwardedMailCountsAsIndependentAuthorshipIsFalse :
      forwardedMailCountsAsIndependentAuthorship ≡ false

    quotedTransportOccurrenceIsPreserved : Bool
    quotedTransportOccurrenceIsPreservedIsTrue :
      quotedTransportOccurrenceIsPreserved ≡ true

    providerIdentityIsUniversalMessageIdentity : Bool
    providerIdentityIsUniversalMessageIdentityIsFalse :
      providerIdentityIsUniversalMessageIdentity ≡ false

    messageTimeEqualsEventTime : Bool
    messageTimeEqualsEventTimeIsFalse :
      messageTimeEqualsEventTime ≡ false

    sourceOmittedWhenParseFails : Bool
    sourceOmittedWhenParseFailsIsFalse :
      sourceOmittedWhenParseFails ≡ false

    candidateInterpretationIsTruth : Bool
    candidateInterpretationIsTruthIsFalse :
      candidateInterpretationIsTruth ≡ false

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse :
      applicabilityPromoted ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

open GenericSourceCompilationBoundary public

canonicalGenericSourceCompilationBoundary : GenericSourceCompilationBoundary
canonicalGenericSourceCompilationBoundary =
  generic-source-compilation-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ProducerCaptureIsSourceIdentity : Set where
data SourceIdentityIsSemanticInterpretation : Set where
data SemanticInterpretationIsOperationalObservation : Set where
data ObserverMetadataIsFreeTextStatement : Set where
data OperationalMetadataIsFreeTextStatement : Set where
data QuoteCreatesIndependentWitness : Set where
data ForwardCreatesIndependentWitness : Set where
data ProviderIdIsUniversalMessageId : Set where
data MessageTimeIsEventTime : Set where
data ParseFailureDeletesSource : Set where
data CandidateInterpretationDeterminesTruth : Set where

producerCaptureDoesNotDetermineSourceIdentity :
  ProducerCaptureIsSourceIdentity → ⊥
producerCaptureDoesNotDetermineSourceIdentity ()

sourceIdentityDoesNotDetermineSemanticInterpretation :
  SourceIdentityIsSemanticInterpretation → ⊥
sourceIdentityDoesNotDetermineSemanticInterpretation ()

semanticInterpretationIsNotOperationalObservation :
  SemanticInterpretationIsOperationalObservation → ⊥
semanticInterpretationIsNotOperationalObservation ()

observerMetadataDoesNotBecomeFreeTextStatement :
  ObserverMetadataIsFreeTextStatement → ⊥
observerMetadataDoesNotBecomeFreeTextStatement ()

operationalMetadataDoesNotBecomeFreeTextStatement :
  OperationalMetadataIsFreeTextStatement → ⊥
operationalMetadataDoesNotBecomeFreeTextStatement ()

quotedMailDoesNotCreateIndependentWitness :
  QuoteCreatesIndependentWitness → ⊥
quotedMailDoesNotCreateIndependentWitness ()

forwardedMailDoesNotCreateIndependentWitness :
  ForwardCreatesIndependentWitness → ⊥
forwardedMailDoesNotCreateIndependentWitness ()

providerIdentityDoesNotBecomeUniversalMessageIdentity :
  ProviderIdIsUniversalMessageId → ⊥
providerIdentityDoesNotBecomeUniversalMessageIdentity ()

messageTimeDoesNotBecomeEventTime :
  MessageTimeIsEventTime → ⊥
messageTimeDoesNotBecomeEventTime ()

parseFailureDoesNotDeleteSource :
  ParseFailureDeletesSource → ⊥
parseFailureDoesNotDeleteSource ()

candidateInterpretationDoesNotDetermineTruth :
  CandidateInterpretationDeterminesTruth → ⊥
candidateInterpretationDoesNotDetermineTruth ()
