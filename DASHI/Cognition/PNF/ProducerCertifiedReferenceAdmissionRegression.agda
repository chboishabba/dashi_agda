module DASHI.Cognition.PNF.ProducerCertifiedReferenceAdmissionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Cognition.PNF.ProducerCertifiedReferenceAdmissionExact


data TinyItem : Set where
  first second : TinyItem

data TinyAuthority : Set where
  admitted : TinyAuthority

referenceOf : TinyItem → TinyAuthority
referenceOf first = admitted
referenceOf second = admitted

AuthoritativeTiny : TinyAuthority → Set
AuthoritativeTiny admitted = ⊤

producerWitness : ∀ item → AuthoritativeTiny (referenceOf item)
producerWitness first = tt
producerWitness second = tt

tinyCertificate : ProducerCertifiedReference TinyItem TinyAuthority
tinyCertificate = record
  { reference = referenceOf
  ; Authoritative = AuthoritativeTiny
  ; producerAuthorityWitness = producerWitness
  }

firstAuthorityPreserved :
  AuthoritativeTiny
    (persistedReference (producerCertifiedRow tinyCertificate first))
firstAuthorityPreserved = producerReferenceIsAuthoritative tinyCertificate first

firstFinalRowExact :
  producerCertifiedRow tinyCertificate first
    ≡ lookupCheckedRow tinyCertificate first
firstFinalRowExact = producerCertifiedReferenceExact tinyCertificate first

zeroPersistentChecksForTwoRows :
  persistentAuthorityLookups (producerCertifiedIntegrityReceipt 2) ≡ zero
zeroPersistentChecksForTwoRows = producerCertificateNeedsNoPerRowLookup 2

perRowPathChecksTwoRows :
  persistentAuthorityLookups (perRowLookupIntegrityReceipt 2) ≡ 2
perRowPathChecksTwoRows = perRowCheckingScalesWithRows 2
