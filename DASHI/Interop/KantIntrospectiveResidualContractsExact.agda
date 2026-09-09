module DASHI.Interop.KantIntrospectiveResidualContractsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- KANT INTROSPECTIVE RESIDUAL CONTRACTS
--
-- Source context: James Michael DuPont explicitly authorised help formalising
-- the discussed Kant work.  The residuals below are intentionally narrower
-- than broad architectural/security claims.  They record the exact gaps that
-- survived review of the live implementation/specification story:
--
--   1. formal specification != deployed runtime conformance;
--   2. integrity/self-certification != relay confidentiality;
--   3. bearer invite possession != revocation/forward secrecy;
--   4. cached/archive checkpoint != recomputed/verified result;
--   5. public/fetchable artifact != licensed/republication-authorised artifact.
--
-- This module does not promote any runtime, cryptographic, or rights claim by
-- construction.  Each residual has its own explicit payment type.
------------------------------------------------------------------------

data KantResidual : Set where
  specRuntimeBindingResidual : KantResidual
  relayConfidentialityResidual : KantResidual
  bearerCapabilityLifecycleResidual : KantResidual
  checkpointTrustResidual : KantResidual
  publicationRightsResidual : KantResidual

record RuntimeConformanceReceipt : Set where
  constructor runtime-conformance-receipt
  field
    specReference : String
    specRevision : String
    runtimeReference : String
    runtimeRevision : String
    vectorSetReference : String
    vectorGeneratorRevision : String
    observedOutputsReference : String
    expectedOutputsReference : String
    coveredSurface : String
    conformsOnCoveredSurface : Bool

open RuntimeConformanceReceipt public

record RelayConfidentialityReceipt : Set where
  constructor relay-confidentiality-receipt
  field
    relayReference : String
    relayRevision : String
    cryptoProfileReference : String
    trafficObservationReference : String
    runtimeBindingReference : String
    integrityObserved : Bool
    confidentialityObserved : Bool
    forwardSecrecyObserved : Bool
    postCompromiseSecurityObserved : Bool

open RelayConfidentialityReceipt public

record CapabilityLifecycleReceipt : Set where
  constructor capability-lifecycle-receipt
  field
    inviteReference : String
    roomReference : String
    issuedGeneration : String
    rotationOrRevocationReference : String
    staleInviteRetestReference : String
    revocationSupported : Bool
    staleInviteRejectedAfterRevocation : Bool
    expirySupported : Bool
    forwardSecrecyEstablishedSeparately : Bool

open CapabilityLifecycleReceipt public

data CheckpointAcceptanceBasis : Set where
  recomputedLocally : CheckpointAcceptanceBasis
  proofVerified : CheckpointAcceptanceBasis
  producerTrustExplicitlyAccepted : CheckpointAcceptanceBasis
  policyExceptionExplicitlyAccepted : CheckpointAcceptanceBasis

record CheckpointTrustReceipt : Set where
  constructor checkpoint-trust-receipt
  field
    checkpointReference : String
    producerReference : String
    inputHeadsReference : String
    algorithmRevision : String
    outputDigest : String
    acceptanceBasis : CheckpointAcceptanceBasis
    verificationReference : String

open CheckpointTrustReceipt public

data RightsBasis : Set where
  ownerAuthored : RightsBasis
  explicitlyLicensed : RightsBasis
  permissionGranted : RightsBasis
  publicDomain : RightsBasis
  thirdPartyRestricted : RightsBasis
  licenseUnknown : RightsBasis

record PublicationRightsReceipt : Set where
  constructor publication-rights-receipt
  field
    artifactReference : String
    artifactDigest : String
    sourceReference : String
    sourceRevision : String
    rightsBasis : RightsBasis
    rightsEvidenceReference : String
    permittedUseReference : String
    publicationTargetReference : String
    exactArtifactBindingReference : String
    publicationAuthorised : Bool

open PublicationRightsReceipt public

data KantResidualPayment : KantResidual → Set where
  paySpecRuntimeBinding :
    RuntimeConformanceReceipt →
    KantResidualPayment specRuntimeBindingResidual

  payRelayConfidentiality :
    RelayConfidentialityReceipt →
    KantResidualPayment relayConfidentialityResidual

  payBearerCapabilityLifecycle :
    CapabilityLifecycleReceipt →
    KantResidualPayment bearerCapabilityLifecycleResidual

  payCheckpointTrust :
    CheckpointTrustReceipt →
    KantResidualPayment checkpointTrustResidual

  payPublicationRights :
    PublicationRightsReceipt →
    KantResidualPayment publicationRightsResidual

record KantIntrospectiveResidualRound (residual : KantResidual) : Set where
  constructor kant-introspective-residual-round
  field
    liveImplementationReference : String
    formalModelReference : String
    visualOrPlainLanguageReviewReference : String
    survivingResidual : KantResidual
    residualIsExact : survivingResidual ≡ residual
    payment : KantResidualPayment residual
    verificationReference : String

open KantIntrospectiveResidualRound public

data SpecProofCreatesRuntimeConformancePermission : Set where
data IntegrityCreatesConfidentialityPermission : Set where
data BearerSecretCreatesForwardSecrecyPermission : Set where
data CachedCheckpointCreatesVerificationPermission : Set where
data PublicArtifactCreatesRepublicationPermission : Set where
data FormalisationPermissionCreatesBlanketRelicensePermission : Set where
data NeighbourArtifactRightsTransferPermission : Set where

specProofDoesNotCreateRuntimeConformance :
  SpecProofCreatesRuntimeConformancePermission → ⊥
specProofDoesNotCreateRuntimeConformance ()

integrityDoesNotCreateConfidentiality :
  IntegrityCreatesConfidentialityPermission → ⊥
integrityDoesNotCreateConfidentiality ()

bearerSecretDoesNotCreateForwardSecrecy :
  BearerSecretCreatesForwardSecrecyPermission → ⊥
bearerSecretDoesNotCreateForwardSecrecy ()

cachedCheckpointDoesNotCreateVerification :
  CachedCheckpointCreatesVerificationPermission → ⊥
cachedCheckpointDoesNotCreateVerification ()

publicArtifactDoesNotCreateRepublicationPermission :
  PublicArtifactCreatesRepublicationPermission → ⊥
publicArtifactDoesNotCreateRepublicationPermission ()

formalisationPermissionDoesNotCreateBlanketRelicense :
  FormalisationPermissionCreatesBlanketRelicensePermission → ⊥
formalisationPermissionDoesNotCreateBlanketRelicense ()

neighbourArtifactRightsDoNotTransfer :
  NeighbourArtifactRightsTransferPermission → ⊥
neighbourArtifactRightsDoNotTransfer ()

record KantResidualBoundary : Set where
  constructor kant-residual-boundary
  field
    specAndRuntimeSeparate : Bool
    integrityAndConfidentialitySeparate : Bool
    capabilityAndForwardSecrecySeparate : Bool
    checkpointAndVerificationSeparate : Bool
    provenanceAndRightsSeparate : Bool
    publicAndRedistributableSeparate : Bool
    formalisationAndRelicensingSeparate : Bool
    rightsBindExactArtifact : Bool

canonicalKantResidualBoundary : KantResidualBoundary
canonicalKantResidualBoundary =
  kant-residual-boundary true true true true true true true true
