module DASHI.Interop.SLRSprint2CanonicalEvidenceConvergenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRSpacyObservationWorldCompilerParityExact
import DASHI.Interop.SLRPostgresWorldPersistenceExact
import DASHI.Interop.SLRReviewedEvidencePaymentExact
import DASHI.Interop.SLRGWBReviewedWikimediaIdentityAndTieredTransportExact

------------------------------------------------------------------------
-- SLR SPRINT 2 — CANONICAL EVIDENCE CONVERGENCE
--
-- The first min-cut is representational, not another producer:
--
-- existing acquisition/retrieval receipts
--   -> one manifestation envelope
--   -> one revision/span/observation substrate
--   -> shared reducer
--   -> reviewed projections.
--
-- The envelope is deliberately incapable of manufacturing semantic authority,
-- legal applicability or claim truth.
------------------------------------------------------------------------

data Sprint2MilestoneState : Set where
  paid : Sprint2MilestoneState
  implementedAwaitingRuntime : Sprint2MilestoneState
  required : Sprint2MilestoneState

m21State : Sprint2MilestoneState
m21State = paid

m22State : Sprint2MilestoneState
m22State = paid

m23State : Sprint2MilestoneState
m23State = implementedAwaitingRuntime

m24State : Sprint2MilestoneState
m24State = required

m25State : Sprint2MilestoneState
m25State = required

m21StateIsPaid : m21State ≡ paid
m21StateIsPaid = refl

m22StateIsPaid : m22State ≡ paid
m22StateIsPaid = refl

m23StateAwaitsRuntime : m23State ≡ implementedAwaitingRuntime
m23StateAwaitsRuntime = refl

record Sprint2Milestone : Set where
  constructor sprint2Milestone
  field
    milestoneReference : String
    state : Sprint2MilestoneState
    capabilityReference : String
    exitReference : String

open Sprint2Milestone public

sprint2Milestones : List Sprint2Milestone
sprint2Milestones =
    sprint2Milestone
      "M2.1"
      m21State
      "one canonical evidence manifestation envelope across structured graph, Wikimedia, legal-authority, PDF, transcript and user evidence families"
      "every manifestation names source, exact revision, content digest and acquisition receipt while remaining candidate-only/non-promoting"
  ∷ sprint2Milestone
      "M2.2"
      m22State
      "one EvidenceManifestation -> SourceRevision -> exact source anchor -> Observation substrate"
      "text evidence uses exact character ranges; structured evidence uses exact structured coordinates; compiler and persisted PG spans retain exact revision identity"
  ∷ sprint2Milestone
      "M2.3"
      m23State
      "shared reducer production ABI"
      "world, matter and law projections consume the same reviewed evidence substrate without internal shortcuts"
  ∷ sprint2Milestone
      "M2.4"
      m24State
      "legal source providers are ordinary producers over the same evidence substrate"
      "PG hit uses zero network; miss acquires/persists; exact second request reuses the stored revision"
  ∷ sprint2Milestone
      "M2.5"
      m25State
      "cross-family exact replay capstone"
      "classification, Australian authority and matter/narrative evidence replay through one source/revision/span/observation/review/projection spine"
  ∷ []

data EvidenceManifestationFamily : Set where
  zelphHyperfabric : EvidenceManifestationFamily
  wikidata : EvidenceManifestationFamily
  wikipedia : EvidenceManifestationFamily
  oalc : EvidenceManifestationFamily
  legalAuthority : EvidenceManifestationFamily
  pdfDocument : EvidenceManifestationFamily
  transcript : EvidenceManifestationFamily
  userEvidence : EvidenceManifestationFamily
  other : EvidenceManifestationFamily

record CanonicalManifestationEnvelopeParity : Set where
  constructor canonicalManifestationEnvelopeParity
  field
    manifestationReferenceExplicit : Bool
    sourceReferenceExplicit : Bool
    exactSourceRevisionExplicit : Bool
    contentDigestExplicit : Bool
    acquisitionReceiptExplicit : Bool
    familyCoordinateExplicit : Bool
    candidateOnlyRequired : Bool
    manifestationCreatesSemanticAuthority : Bool
    manifestationPromotesApplicability : Bool
    manifestationPromotesClaimTruth : Bool

open CanonicalManifestationEnvelopeParity public

canonicalManifestationEnvelope : CanonicalManifestationEnvelopeParity
canonicalManifestationEnvelope =
  canonicalManifestationEnvelopeParity
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false

record CurrentM21ImplementationParity : Set where
  constructor currentM21ImplementationParity
  field
    coreOwnsEnvelope : Bool
    wikidataAdapterUsesEnvelope : Bool
    wikipediaAdapterUsesEnvelope : Bool
    oalcAdapterUsesEnvelope : Bool
    oneCrossFamilyTestUsesSameEnvelope : Bool
    spanSubstrateAlreadyClaimedPaid : Bool
    sharedReducerAlreadyClaimedPaid : Bool

open CurrentM21ImplementationParity public

currentM21Implementation : CurrentM21ImplementationParity
currentM21Implementation =
  currentM21ImplementationParity
    true
    true
    true
    true
    true
    true
    false

data EvidenceSpanKind : Set where
  textRange : EvidenceSpanKind
  structuredCoordinate : EvidenceSpanKind
  wholeRevision : EvidenceSpanKind

record CanonicalSourceSpanObservationParity : Set where
  constructor canonicalSourceSpanObservationParity
  field
    sourceRevisionRetainsManifestationIdentity : Bool
    sourceRevisionRetainsContentDigest : Bool
    sourceRevisionRetainsRevisionReceipt : Bool
    textEvidenceUsesExactCharacterRange : Bool
    graphEvidenceUsesStructuredCoordinate : Bool
    graphEvidenceRequiresFabricatedTextRange : Bool
    observationRevisionMustEqualSpanRevision : Bool
    worldObservationLowersToCanonicalObservation : Bool
    compilerTokenRequiresPrecedingExactRevision : Bool
    compilerMaySwitchDocumentRevisionMidStream : Bool
    compilerWireVersionChangedForThisWeld : Bool
    postgresRevisionSpanWeldImplemented : Bool

open CanonicalSourceSpanObservationParity public

currentM22PartialParity : CanonicalSourceSpanObservationParity
currentM22PartialParity =
  canonicalSourceSpanObservationParity
    true
    true
    true
    true
    true
    false
    true
    true
    true
    false
    false
    true

record Sprint2ExitGate : Set where
  constructor sprint2ExitGate
  field
    oneManifestationEnvelopeImplemented : Bool
    oneSourceRevisionSpanObservationSubstrateImplemented : Bool
    sharedReducerImplemented : Bool
    legalProvidersOrdinaryProducerImplemented : Bool
    crossFamilyReplayCapstoneImplemented : Bool
    exactRustRuntimeReceiptObserved : Bool
    exactAgdaKernelReceiptObserved : Bool
    persistedReplayReceiptObserved : Bool
    sprintMayBeDeclaredClosed : Bool

open Sprint2ExitGate public

currentSprint2ExitGate : Sprint2ExitGate
currentSprint2ExitGate =
  sprint2ExitGate
    true
    true
    true
    false
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ManifestationCreatesSemanticAuthority : Set where
data ManifestationPromotesApplicability : Set where
data ManifestationPromotesClaimTruth : Set where
data ProducerSpecificEnvelopeBypassesCanonicalEnvelope : Set where
data ManifestationEnvelopeMeansSpanConvergencePaid : Set where
data StructuredEvidenceRequiresFakeTextSpan : Set where
data TokenMayCompileWithoutExactRevision : Set where

manifestationCannotCreateSemanticAuthority :
  ManifestationCreatesSemanticAuthority → ⊥
manifestationCannotCreateSemanticAuthority ()

manifestationCannotPromoteApplicability :
  ManifestationPromotesApplicability → ⊥
manifestationCannotPromoteApplicability ()

manifestationCannotPromoteClaimTruth :
  ManifestationPromotesClaimTruth → ⊥
manifestationCannotPromoteClaimTruth ()

producerSpecificEnvelopeCannotBypassCanonicalEnvelope :
  ProducerSpecificEnvelopeBypassesCanonicalEnvelope → ⊥
producerSpecificEnvelopeCannotBypassCanonicalEnvelope ()

manifestationEnvelopeDoesNotPaySpanConvergence :
  ManifestationEnvelopeMeansSpanConvergencePaid → ⊥
manifestationEnvelopeDoesNotPaySpanConvergence ()


structuredEvidenceDoesNotRequireFakeTextSpan :
  StructuredEvidenceRequiresFakeTextSpan → ⊥
structuredEvidenceDoesNotRequireFakeTextSpan ()

tokenCannotCompileWithoutExactRevision :
  TokenMayCompileWithoutExactRevision → ⊥
tokenCannotCompileWithoutExactRevision ()
