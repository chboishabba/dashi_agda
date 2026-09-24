module DASHI.Wikimedia.JmdLeanGoldenAbiAttachmentExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.JmdLeanIntegratedMachineLineageExact as Machine
open import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact
open import DASHI.Wikimedia.LeanWikidataVerificationExact

------------------------------------------------------------------------
-- CONCRETE JMD LEAN DECLARATIONS -> GOLDEN AGDA BIDI ABI
------------------------------------------------------------------------

record JmdGetterSurface : Set where
  constructor jmd-getter-surface
  field
    getterMachine : Machine.JmdLeanIntegratedMachine
    entityUrlBinding : Machine.IntegratedDeclarationBinding
    fetchJsonBinding : Machine.IntegratedDeclarationBinding
    fetchEntityBinding : Machine.IntegratedDeclarationBinding
    scanArticleBinding : Machine.IntegratedDeclarationBinding
    enrichBinding : Machine.IntegratedDeclarationBinding
    getterSurfaceUsesIntegratedMachine : Bool
    getterSurfaceCreatesWorldTruth : Bool
    getterSurfaceCreatesSemanticAuthority : Bool

open JmdGetterSurface public

canonicalJmdGetterSurface : JmdGetterSurface
canonicalJmdGetterSurface =
  jmd-getter-surface
    Machine.canonicalJmdLeanIntegratedMachine
    Machine.entityDataUrlIntegrated
    Machine.fetchEntityJsonIntegrated
    Machine.fetchEntityIntegrated
    Machine.scanArticleIntegrated
    Machine.cmdEnrichIntegrated
    true false false

record JmdVerificationSurface : Set where
  constructor jmd-verification-surface
  field
    verificationMachine : Machine.JmdLeanIntegratedMachine
    leanCompilerBinding : Machine.IntegratedDeclarationBinding
    subChainSoundBinding : Machine.IntegratedDeclarationBinding
    verificationSurfaceUsesIntegratedMachine : Bool
    verificationSurfaceCreatesWorldTruth : Bool
    verificationSurfaceCreatesSemanticAuthority : Bool
    verificationSurfaceCreatesAgdaProof : Bool

open JmdVerificationSurface public

canonicalJmdVerificationSurface : JmdVerificationSurface
canonicalJmdVerificationSurface =
  jmd-verification-surface
    Machine.canonicalJmdLeanIntegratedMachine
    Machine.cmdLeanIntegrated
    Machine.checkSubChainSoundIntegrated
    true false false false

record JmdPublicationSurface : Set where
  constructor jmd-publication-surface
  field
    publicationMachine : Machine.JmdLeanIntegratedMachine
    reportCsvBinding : Machine.IntegratedDeclarationBinding
    worklistCsvBinding : Machine.IntegratedDeclarationBinding
    publicationSurfaceUsesIntegratedMachine : Bool
    publicationSurfaceCreatesKernelStatus : Bool
    publicationSurfaceCreatesWorldTruth : Bool

open JmdPublicationSurface public

canonicalJmdPublicationSurface : JmdPublicationSurface
canonicalJmdPublicationSurface =
  jmd-publication-surface
    Machine.canonicalJmdLeanIntegratedMachine
    Machine.csvOfRowsIntegrated
    Machine.worklistCsvIntegrated
    true false false

------------------------------------------------------------------------
-- Runtime-shaped receipt ABIs.
------------------------------------------------------------------------

record JmdGetterAbiReceipt : Set where
  constructor jmd-getter-abi-receipt
  field
    getterReceiptSurface : JmdGetterSurface
    normalizedObservation : WorldObservation
    getterProducerDeclarationReference : String
    getterReceiptReference : String
    getterReceiptCreatesWorldTruth : Bool
    getterReceiptCreatesSemanticAuthority : Bool

open JmdGetterAbiReceipt public

mkJmdGetterAbiReceipt : WorldObservation → String → String → JmdGetterAbiReceipt
mkJmdGetterAbiReceipt observation producer receipt =
  jmd-getter-abi-receipt
    canonicalJmdGetterSurface observation producer receipt false false

record JmdVerificationAbiReceipt : Set where
  constructor jmd-verification-abi-receipt
  field
    verificationReceiptSurface : JmdVerificationSurface
    attachedVerification : LeanVerificationReceipt
    verificationProducerDeclarationReference : String
    verificationAbiReceiptReference : String
    verificationReceiptCreatesWorldTruth : Bool
    verificationReceiptCreatesSemanticAuthority : Bool
    verificationReceiptCreatesAgdaProof : Bool

open JmdVerificationAbiReceipt public

mkJmdVerificationAbiReceipt :
  LeanVerificationReceipt → String → String → JmdVerificationAbiReceipt
mkJmdVerificationAbiReceipt verification producer receipt =
  jmd-verification-abi-receipt
    canonicalJmdVerificationSurface verification producer receipt false false false

record JmdPublicationAbiReceipt : Set where
  constructor jmd-publication-abi-receipt
  field
    publicationReceiptSurface : JmdPublicationSurface
    artifactReference : String
    publicationProducerDeclarationReference : String
    publicationAbiReceiptReference : String
    publicationReceiptCreatesKernelStatus : Bool
    publicationReceiptCreatesWorldTruth : Bool

open JmdPublicationAbiReceipt public

mkJmdPublicationAbiReceipt : String → String → String → JmdPublicationAbiReceipt
mkJmdPublicationAbiReceipt artifact producer receipt =
  jmd-publication-abi-receipt
    canonicalJmdPublicationSurface artifact producer receipt false false

------------------------------------------------------------------------
-- Cross-layer non-collapse firewalls.
------------------------------------------------------------------------

data GetterDeclarationEqualsWorldObservation : Set where
data VerificationDeclarationEqualsKernelReceipt : Set where
data PublicationArtifactEqualsKernelStatus : Set where
data IntegratedMachineEqualsWorldTruth : Set where

getterDeclarationDoesNotEqualWorldObservation :
  GetterDeclarationEqualsWorldObservation → ⊥
getterDeclarationDoesNotEqualWorldObservation ()

verificationDeclarationDoesNotEqualKernelReceipt :
  VerificationDeclarationEqualsKernelReceipt → ⊥
verificationDeclarationDoesNotEqualKernelReceipt ()

publicationArtifactDoesNotEqualKernelStatus :
  PublicationArtifactEqualsKernelStatus → ⊥
publicationArtifactDoesNotEqualKernelStatus ()

integratedMachineDoesNotEqualWorldTruth :
  IntegratedMachineEqualsWorldTruth → ⊥
integratedMachineDoesNotEqualWorldTruth ()
