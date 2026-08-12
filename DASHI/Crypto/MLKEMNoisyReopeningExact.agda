module DASHI.Crypto.MLKEMNoisyReopeningExact where

------------------------------------------------------------------------
-- ML-KEM / MODULE-LWE NOISY REOPENING CORE
--
-- Primary standard:
-- National Institute of Standards and Technology; Gorjan Alagic, Quynh Dang,
-- Dustin Moody, Angela Robinson, Hamilton Silberg, Daniel Smith-Tone,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Foundational LWE reference:
-- Oded Regev, "On lattices, learning with errors, random linear codes, and
-- cryptography", STOC 2005, pp. 84-93. DOI: 10.1145/1060590.1060603.
--
-- The exact ML-KEM algorithms are not reimplemented here.  This module
-- formalises the DASHI-native structural core needed by the thread:
--   public structured observation = signal + controlled residual,
--   public observation need not identify a unique hidden decomposition,
--   an authorised receipt can reopen the intended fine state exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as Quotient

------------------------------------------------------------------------
-- Generic noisy structured observation.
------------------------------------------------------------------------

record NoisyStructuredObservation : Set₁ where
  constructor noisyStructuredObservation
  field
    Secret Error Public : Set
    signal : Secret → Public
    addError : Public → Error → Public
    observe : Secret → Error → Public
    observeIsSignalPlusResidual :
      ∀ secret error →
      observe secret error ≡ addError (signal secret) error

open NoisyStructuredObservation public

FineState : NoisyStructuredObservation → Set
FineState system = Secret system × Error system

------------------------------------------------------------------------
-- A collision is the exact finite witness for a broad public fibre:
-- two distinct hidden decompositions produce the same public observation.
------------------------------------------------------------------------

record PublicFibreCollision
    (system : NoisyStructuredObservation) : Set where
  constructor publicFibreCollision
  field
    firstSecret secondSecret : Secret system
    firstError secondError : Error system
    samePublic :
      observe system firstSecret firstError
      ≡ observe system secondSecret secondError
    hiddenDistinct :
      (firstSecret ≡ secondSecret × firstError ≡ secondError) → ⊥

open PublicFibreCollision public

------------------------------------------------------------------------
-- Concrete arithmetic toy: y = 2*s + e.
--
-- (s,e)=(0,2) and (1,0) both expose y=2.  This is NOT an ML-KEM security
-- instance; it is an executable witness that "public structured value" does
-- not logically entail a unique signal/residual decomposition.
------------------------------------------------------------------------

toyNoisyObservation : NoisyStructuredObservation
toyNoisyObservation =
  noisyStructuredObservation
    Nat Nat Nat
    (λ s → 2 * s)
    _+_
    (λ s e → 2 * s + e)
    (λ s e → refl)
  where
    open import Data.Nat.Base using (_+_; _*_)

toyPublicCollision : PublicFibreCollision toyNoisyObservation
toyPublicCollision =
  publicFibreCollision 0 1 2 0 refl distinct
  where
    open import Data.Nat.Base using (zero; suc)
    distinct : (0 ≡ 1 × 2 ≡ 0) → ⊥
    distinct ((), second)

------------------------------------------------------------------------
-- Authorised exact reopening: retain the hidden coordinate as a private
-- receipt.  The public projection is intentionally many-to-one in the toy.
------------------------------------------------------------------------

toyCore : Fibre.FibreRestrictionCore
toyCore =
  Fibre.fibreRestrictionCore
    (Nat × Nat)
    Nat
    Nat
    (λ pair → 2 * Data.Product.proj₁ pair + Data.Product.proj₂ pair)
    (λ surface → Nat × Nat)
    (λ evidence surface → Nat × Nat)
    true
    false
  where
    open import Data.Nat.Base using (_+_; _*_)

toyNoisyProvenanceQuotient : Quotient.ProvenanceBearingQuotient toyCore
toyNoisyProvenanceQuotient =
  Quotient.provenanceBearingQuotient
    (Nat × Nat)
    (λ pair → pair)
    (λ surface receipt → receipt)
    (λ pair → refl)

------------------------------------------------------------------------
-- KEM-shaped correctness contract.  This is the exact structural statement
-- needed for "ML-KEM hides the lift, not the projection": encapsulation may be
-- public, while decapsulation correctness is tied to the authorised secret
-- coordinate.  Hardness remains a separate assumption/model-relative claim.
------------------------------------------------------------------------

record CorrectKEM : Set₁ where
  constructor correctKEM
  field
    PublicKey SecretKey Coins Ciphertext SharedSecret : Set
    derivePublic : SecretKey → PublicKey
    encapsulate : PublicKey → Coins → Ciphertext × SharedSecret
    decapsulate : SecretKey → Ciphertext → SharedSecret
    correctness :
      ∀ secret coins →
      let result = encapsulate (derivePublic secret) coins in
      decapsulate secret (Data.Product.proj₁ result)
      ≡ Data.Product.proj₂ result

open CorrectKEM public

record MLKEMClaimBoundary : Set where
  constructor mlkemClaimBoundary
  field
    publicNoiseMeansInformationDestroyed : Bool
    publicNoiseMeansInformationDestroyedIsFalse :
      publicNoiseMeansInformationDestroyed ≡ false
    publicObservationUniquelyDeterminesHiddenState : Bool
    publicObservationUniquelyDeterminesHiddenStateIsFalse :
      publicObservationUniquelyDeterminesHiddenState ≡ false
    thisModuleProvesMLKEMSecurity : Bool
    thisModuleProvesMLKEMSecurityIsFalse : thisModuleProvesMLKEMSecurity ≡ false

canonicalMLKEMClaimBoundary : MLKEMClaimBoundary
canonicalMLKEMClaimBoundary =
  mlkemClaimBoundary false refl false refl false refl
