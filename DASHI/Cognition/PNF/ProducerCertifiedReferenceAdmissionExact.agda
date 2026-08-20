module DASHI.Cognition.PNF.ProducerCertifiedReferenceAdmissionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)

------------------------------------------------------------------------
-- Producer-certified reference admission.
--
-- Runtime motivation: after producer-complete dependency-head admission removed
-- the persistent self-rewrite, PostgreSQL flame attribution exposed the next
-- physical cost as per-row referential-integrity/SPI and index work.  This
-- theorem separates the semantic obligation "the emitted reference belongs to
-- the authority carrier" from one particular physical realization of that
-- obligation (for example, a database lookup for every emitted row).
--
-- Nothing here licenses disabling an arbitrary foreign key.  The alternative
-- realization is admissible only for a named producer that carries an exact
-- authority witness for every emitted reference.
------------------------------------------------------------------------

record ProducerCertifiedReference
  (Item Reference : Set)
  : Set₁ where
  field
    reference : Item → Reference
    Authoritative : Reference → Set
    producerAuthorityWitness :
      ∀ item → Authoritative (reference item)

open ProducerCertifiedReference public

record PersistentReferenceRow
  (Item Reference : Set)
  : Set where
  constructor referenceRow
  field
    item : Item
    persistedReference : Reference

open PersistentReferenceRow public

-- A producer-certified first-write row carries exactly the producer reference.
producerCertifiedRow :
  ∀ {Item Reference : Set} →
  ProducerCertifiedReference Item Reference →
  Item →
  PersistentReferenceRow Item Reference
producerCertifiedRow certificate item =
  referenceRow item (reference certificate item)

-- Abstract final row after a per-row authority lookup/check.  Successful
-- checking cannot change the referenced value; it only supplies another proof
-- that the same value belongs to the authority carrier.
lookupCheckedRow :
  ∀ {Item Reference : Set} →
  ProducerCertifiedReference Item Reference →
  Item →
  PersistentReferenceRow Item Reference
lookupCheckedRow certificate item =
  referenceRow item (reference certificate item)

producerCertifiedReferenceExact :
  ∀ {Item Reference : Set}
    (certificate : ProducerCertifiedReference Item Reference)
    (item : Item) →
  producerCertifiedRow certificate item ≡ lookupCheckedRow certificate item
producerCertifiedReferenceExact certificate item = refl

-- The semantic membership obligation is discharged directly by producer
-- evidence, independently of whether a physical authority lookup is performed.
producerReferenceIsAuthoritative :
  ∀ {Item Reference : Set}
    (certificate : ProducerCertifiedReference Item Reference)
    (item : Item) →
  Authoritative certificate
    (persistedReference (producerCertifiedRow certificate item))
producerReferenceIsAuthoritative certificate item =
  producerAuthorityWitness certificate item

-- Every consumer of the final persisted row observes the same result under the
-- producer-certified and per-row-lookup realizations.
consumerObservationExact :
  ∀ {Item Reference Observation : Set}
    (certificate : ProducerCertifiedReference Item Reference)
    (observe : PersistentReferenceRow Item Reference → Observation)
    (item : Item) →
  observe (producerCertifiedRow certificate item)
    ≡ observe (lookupCheckedRow certificate item)
consumerObservationExact certificate observe item = refl

------------------------------------------------------------------------
-- Physical integrity realization receipts.
--
-- These counters are deliberately separate from semantic authority.  They say
-- that, once producer evidence exists, the authority-membership theorem itself
-- does not require one persistent reference lookup per row.  A concrete runtime
-- may still retain database FKs for recovery, generic writers or other policy
-- reasons; those are additional obligations, not consequences of this theorem.
------------------------------------------------------------------------

record ReferenceIntegrityReceipt : Set where
  constructor integrityReceipt
  field
    admittedRows : Nat
    persistentAuthorityLookups : Nat

open ReferenceIntegrityReceipt public

producerCertifiedIntegrityReceipt : Nat → ReferenceIntegrityReceipt
producerCertifiedIntegrityReceipt count = integrityReceipt count zero

perRowLookupIntegrityReceipt : Nat → ReferenceIntegrityReceipt
perRowLookupIntegrityReceipt count = integrityReceipt count count

producerCertificateNeedsNoPerRowLookup :
  ∀ count →
  persistentAuthorityLookups (producerCertifiedIntegrityReceipt count) ≡ zero
producerCertificateNeedsNoPerRowLookup count = refl

perRowCheckingScalesWithRows :
  ∀ count →
  persistentAuthorityLookups (perRowLookupIntegrityReceipt count) ≡ count
perRowCheckingScalesWithRows count = refl

record ProducerCertifiedReferenceAdmission
  (Item Reference : Set)
  : Set₁ where
  field
    certificate : ProducerCertifiedReference Item Reference
    authorityPreserved :
      ∀ item →
      Authoritative certificate
        (persistedReference (producerCertifiedRow certificate item))
    finalRowExact :
      ∀ item →
      producerCertifiedRow certificate item ≡ lookupCheckedRow certificate item
    noSemanticPerRowLookupRequirement :
      ∀ count →
      persistentAuthorityLookups
        (producerCertifiedIntegrityReceipt count) ≡ zero

open ProducerCertifiedReferenceAdmission public

compileProducerCertifiedReferenceAdmission :
  ∀ {Item Reference : Set}
    (certificate : ProducerCertifiedReference Item Reference) →
  ProducerCertifiedReferenceAdmission Item Reference
compileProducerCertifiedReferenceAdmission certificate = record
  { certificate = certificate
  ; authorityPreserved = producerReferenceIsAuthoritative certificate
  ; finalRowExact = producerCertifiedReferenceExact certificate
  ; noSemanticPerRowLookupRequirement = producerCertificateNeedsNoPerRowLookup
  }
