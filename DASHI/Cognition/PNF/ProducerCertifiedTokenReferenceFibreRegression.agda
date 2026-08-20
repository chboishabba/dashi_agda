module DASHI.Cognition.PNF.ProducerCertifiedTokenReferenceFibreRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Cognition.PNF.ProducerCertifiedTokenReferenceFibreExact

natAuthority : TokenReferenceAuthority Nat Nat
natAuthority = record
  { SymbolAuthoritative = λ _ → ⊤
  ; OriginAuthoritative = λ _ → ⊤
  }

sampleReferences : TokenReferenceFibre Nat Nat
sampleReferences =
  tokenReferenceFibre
    11 12 13 14 15
    1 1 3 1

sampleCertificate : ProducerCertifiedTokenReferences Nat Nat natAuthority
sampleCertificate = record
  { references = sampleReferences
  ; orthSymbolWitness = tt
  ; lemmaSymbolWitness = tt
  ; posSymbolWitness = tt
  ; tagSymbolWitness = tt
  ; dependencySymbolWitness = tt
  ; lemmaOriginWitness = tt
  ; posOriginWitness = tt
  ; tagOriginWitness = tt
  ; dependencyOriginWitness = tt
  }

sampleFinalReferenceFibreExact :
  producerCertifiedTokenRow sampleCertificate
    ≡ lookupCheckedTokenRow sampleCertificate
sampleFinalReferenceFibreExact =
  producerCertifiedTokenReferenceExact sampleCertificate

sampleConsumerExact :
  orthSymbol (producerCertifiedTokenRow sampleCertificate)
    ≡ orthSymbol (lookupCheckedTokenRow sampleCertificate)
sampleConsumerExact =
  consumerObservationExact sampleCertificate orthSymbol

sampleProducerOrthChecksZero :
  orthSymbolLookups (producerCertifiedLookupReceipt 7) ≡ zero
sampleProducerOrthChecksZero =
  producerCertifiedHasNoPerRowSymbolLookups 7

sampleProducerOriginChecksZero :
  dependencyOriginLookups (producerCertifiedLookupReceipt 7) ≡ zero
sampleProducerOriginChecksZero =
  producerCertifiedHasNoPerRowOriginLookups 7

sampleLegacyOrthChecksSeven :
  orthSymbolLookups (perRowForeignKeyLookupReceipt 7) ≡ 7
sampleLegacyOrthChecksSeven = refl

sampleLegacyOriginChecksSeven :
  dependencyOriginLookups (perRowForeignKeyLookupReceipt 7) ≡ 7
sampleLegacyOriginChecksSeven = refl
