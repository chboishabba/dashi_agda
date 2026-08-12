module DASHI.Crypto.ReopeningArchitectureExact where

------------------------------------------------------------------------
-- CRYPTOGRAPHIC REOPENING ARCHITECTURE
--
-- References / provenance:
-- Peter W. Shor, "Polynomial-Time Algorithms for Prime Factorization and
-- Discrete Logarithms on a Quantum Computer", SIAM J. Comput. 26(5), 1997.
-- DOI: 10.1137/S0097539795293172.
--
-- National Institute of Standards and Technology; Gorjan Alagic, Quynh Dang,
-- Dustin Moody, Angela Robinson, Hamilton Silberg, Daniel Smith-Tone,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- This module formalises only the shared structural distinction used in DASHI:
-- reversible authorised reopening versus computationally unavailable reopening
-- for another model.  It does NOT implement RSA, ML-KEM, AES, QKD, or prove a
-- cryptographic hardness assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)

record SecretReopeningSystem : Set₁ where
  constructor secretReopeningSystem
  field
    Plain Cipher Key : Set
    encrypt : Plain → Key → Cipher
    decrypt : Cipher → Key → Plain
    authorisedRoundTrip : ∀ message key → decrypt (encrypt message key) key ≡ message

open SecretReopeningSystem public

record KeyEncapsulationSystem : Set₁ where
  constructor keyEncapsulationSystem
  field
    PublicKey SecretKey Ciphertext SharedSecret : Set
    encapsulate : PublicKey → Ciphertext × SharedSecret
    decapsulate : SecretKey → Ciphertext → SharedSecret

open KeyEncapsulationSystem public

record ModelRelativeReopening : Set₁ where
  constructor modelRelativeReopening
  field
    Model Visible Hidden : Set
    reopenCost : Model → Visible → Hidden → Nat

open ModelRelativeReopening public

record ReopeningAsymmetry (system : ModelRelativeReopening) : Set₁ where
  constructor reopeningAsymmetry
  field
    authorised adversarial : Model system
    visible : Visible system
    hidden : Hidden system
    authorisedCost adversarialCost : Nat
    authorisedExact : reopenCost system authorised visible hidden ≡ authorisedCost
    adversarialExact : reopenCost system adversarial visible hidden ≡ adversarialCost

open ReopeningAsymmetry public

data HiddenFibreMode : Set where
  informationTheoretic
  secretCoordinateTransform
  algebraicTrapdoor
  noisyModuleGeometry : HiddenFibreMode

record CandidateVerifier : Set₁ where
  constructor candidateVerifier
  field
    Instance Candidate : Set
    verifies : Instance → Candidate → Set

open CandidateVerifier public

record SecretSection : Set₁ where
  constructor secretSection
  field
    Surface Fine Secret : Set
    project : Fine → Surface
    lift : Surface → Secret → Fine

open SecretSection public
