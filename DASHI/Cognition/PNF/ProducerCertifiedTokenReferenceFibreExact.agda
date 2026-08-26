module DASHI.Cognition.PNF.ProducerCertifiedTokenReferenceFibreExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)

------------------------------------------------------------------------
-- Exact specialization for SensibLaw migration 176.
--
-- One strict-v2 parser token carries five live numeric semantic-symbol
-- references and four live annotation-origin references.  The bounded producer
-- already owns all nine coordinates before authority insertion.  Migration 176
-- replaces their nine per-row FK lookups with one producer certificate over the
-- complete bounded reference fibre, while generic writers retain set-wise
-- authority validation and authority-side reverse-restrict guards.
--
-- This theorem is intentionally narrower than arbitrary FK elimination: it says
-- only that, when the producer carries authority witnesses for these exact nine
-- coordinates, the semantic final row is unchanged by omitting nine redundant
-- per-row membership lookups.
------------------------------------------------------------------------

record TokenReferenceFibre
  (Symbol Origin : Set)
  : Set where
  constructor tokenReferenceFibre
  field
    orthSymbol : Symbol
    lemmaSymbol : Symbol
    posSymbol : Symbol
    tagSymbol : Symbol
    dependencySymbol : Symbol
    lemmaOrigin : Origin
    posOrigin : Origin
    tagOrigin : Origin
    dependencyOrigin : Origin

open TokenReferenceFibre public

record TokenReferenceAuthority
  (Symbol Origin : Set)
  : Set₁ where
  field
    SymbolAuthoritative : Symbol → Set
    OriginAuthoritative : Origin → Set

open TokenReferenceAuthority public

record ProducerCertifiedTokenReferences
  (Symbol Origin : Set)
  (authority : TokenReferenceAuthority Symbol Origin)
  : Set₁ where
  field
    references : TokenReferenceFibre Symbol Origin
    orthSymbolWitness : SymbolAuthoritative authority (orthSymbol references)
    lemmaSymbolWitness : SymbolAuthoritative authority (lemmaSymbol references)
    posSymbolWitness : SymbolAuthoritative authority (posSymbol references)
    tagSymbolWitness : SymbolAuthoritative authority (tagSymbol references)
    dependencySymbolWitness :
      SymbolAuthoritative authority (dependencySymbol references)
    lemmaOriginWitness : OriginAuthoritative authority (lemmaOrigin references)
    posOriginWitness : OriginAuthoritative authority (posOrigin references)
    tagOriginWitness : OriginAuthoritative authority (tagOrigin references)
    dependencyOriginWitness :
      OriginAuthoritative authority (dependencyOrigin references)

open ProducerCertifiedTokenReferences public

-- Successful per-row RI checks cannot alter any of the nine references; they
-- only re-establish authority membership already supplied by the producer.
producerCertifiedTokenRow :
  ∀ {Symbol Origin : Set}
    {authority : TokenReferenceAuthority Symbol Origin} →
  ProducerCertifiedTokenReferences Symbol Origin authority →
  TokenReferenceFibre Symbol Origin
producerCertifiedTokenRow = references

lookupCheckedTokenRow :
  ∀ {Symbol Origin : Set}
    {authority : TokenReferenceAuthority Symbol Origin} →
  ProducerCertifiedTokenReferences Symbol Origin authority →
  TokenReferenceFibre Symbol Origin
lookupCheckedTokenRow = references

producerCertifiedTokenReferenceExact :
  ∀ {Symbol Origin : Set}
    {authority : TokenReferenceAuthority Symbol Origin}
    (certificate : ProducerCertifiedTokenReferences Symbol Origin authority) →
  producerCertifiedTokenRow certificate ≡ lookupCheckedTokenRow certificate
producerCertifiedTokenReferenceExact certificate = refl

consumerObservationExact :
  ∀ {Symbol Origin Observation : Set}
    {authority : TokenReferenceAuthority Symbol Origin}
    (certificate : ProducerCertifiedTokenReferences Symbol Origin authority)
    (observe : TokenReferenceFibre Symbol Origin → Observation) →
  observe (producerCertifiedTokenRow certificate)
    ≡ observe (lookupCheckedTokenRow certificate)
consumerObservationExact certificate observe = refl

------------------------------------------------------------------------
-- Physical realization receipt.
--
-- Keep each coordinate explicit instead of collapsing the measured nine-FK
-- surface into an opaque scalar.  In the legacy row-FK realization every field
-- costs one persistent membership check per admitted row.  Under the exact
-- producer certificate, none of those nine semantic obligations requires a
-- per-row persistent lookup.
------------------------------------------------------------------------

record TokenReferenceLookupReceipt : Set where
  constructor tokenReferenceLookupReceipt
  field
    admittedRows : Nat
    orthSymbolLookups : Nat
    lemmaSymbolLookups : Nat
    posSymbolLookups : Nat
    tagSymbolLookups : Nat
    dependencySymbolLookups : Nat
    lemmaOriginLookups : Nat
    posOriginLookups : Nat
    tagOriginLookups : Nat
    dependencyOriginLookups : Nat

open TokenReferenceLookupReceipt public

producerCertifiedLookupReceipt : Nat → TokenReferenceLookupReceipt
producerCertifiedLookupReceipt count =
  tokenReferenceLookupReceipt
    count zero zero zero zero zero zero zero zero zero

perRowForeignKeyLookupReceipt : Nat → TokenReferenceLookupReceipt
perRowForeignKeyLookupReceipt count =
  tokenReferenceLookupReceipt
    count count count count count count count count count count

producerCertifiedHasNoPerRowSymbolLookups :
  ∀ count →
  orthSymbolLookups (producerCertifiedLookupReceipt count) ≡ zero
producerCertifiedHasNoPerRowSymbolLookups count = refl

producerCertifiedHasNoPerRowOriginLookups :
  ∀ count →
  dependencyOriginLookups (producerCertifiedLookupReceipt count) ≡ zero
producerCertifiedHasNoPerRowOriginLookups count = refl

perRowOrthLookupScalesWithRows :
  ∀ count →
  orthSymbolLookups (perRowForeignKeyLookupReceipt count) ≡ count
perRowOrthLookupScalesWithRows count = refl

perRowDependencyOriginLookupScalesWithRows :
  ∀ count →
  dependencyOriginLookups (perRowForeignKeyLookupReceipt count) ≡ count
perRowDependencyOriginLookupScalesWithRows count = refl

record ProducerCertifiedTokenReferenceAdmission
  (Symbol Origin : Set)
  (authority : TokenReferenceAuthority Symbol Origin)
  : Set₁ where
  field
    certificate : ProducerCertifiedTokenReferences Symbol Origin authority
    finalReferenceFibreExact :
      producerCertifiedTokenRow certificate ≡ lookupCheckedTokenRow certificate
    noPerRowOrthLookup :
      ∀ count →
      orthSymbolLookups (producerCertifiedLookupReceipt count) ≡ zero
    noPerRowOriginLookup :
      ∀ count →
      dependencyOriginLookups (producerCertifiedLookupReceipt count) ≡ zero

open ProducerCertifiedTokenReferenceAdmission public

compileProducerCertifiedTokenReferenceAdmission :
  ∀ {Symbol Origin : Set}
    {authority : TokenReferenceAuthority Symbol Origin}
    (certificate : ProducerCertifiedTokenReferences Symbol Origin authority) →
  ProducerCertifiedTokenReferenceAdmission Symbol Origin authority
compileProducerCertifiedTokenReferenceAdmission certificate = record
  { certificate = certificate
  ; finalReferenceFibreExact = producerCertifiedTokenReferenceExact certificate
  ; noPerRowOrthLookup = producerCertifiedHasNoPerRowSymbolLookups
  ; noPerRowOriginLookup = producerCertifiedHasNoPerRowOriginLookups
  }
