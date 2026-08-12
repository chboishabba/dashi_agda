module DASHI.Crypto.KEMStateContractExact where

------------------------------------------------------------------------
-- KEM STATE CONTRACTS
--
-- Primary references:
-- National Institute of Standards and Technology et al.,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Gorjan Alagic, Elaine Barker, Lily Chen, Dustin Moody, Angela Robinson,
-- Hamilton Silberg, Noah Waller,
-- "Recommendations for Key-Encapsulation Mechanisms", NIST SP 800-227,
-- 2025. DOI: 10.6028/NIST.SP.800-227.
--
-- This module treats a KEM as a state machine with explicit preconditions,
-- postconditions and invariants.  It does not model implementation leakage.
-- Agreement is a trace predicate rather than an axiom for every seed/coin pair:
-- lattice KEMs may have a nonzero (negligible) decapsulation-failure probability.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)

record KEMStateMachine : Set₁ where
  constructor kemStateMachine
  field
    KeyGenSeed EncapsCoins PublicKey SecretKey Ciphertext SharedSecret : Set

    keyGen : KeyGenSeed → PublicKey × SecretKey
    encapsulate : PublicKey → EncapsCoins → Ciphertext × SharedSecret
    decapsulate : SecretKey → Ciphertext → SharedSecret

    ValidPublicKey : PublicKey → Set
    ValidSecretKey : SecretKey → Set
    ValidCiphertext : Ciphertext → Set
    KeyPairRelation : PublicKey → SecretKey → Set

    keyGenPostcondition :
      ∀ seed →
      let pair = keyGen seed in
      ValidPublicKey (proj₁ pair)
      × (ValidSecretKey (proj₂ pair) × KeyPairRelation (proj₁ pair) (proj₂ pair))

    encapsulationPostcondition :
      ∀ {pk} → ValidPublicKey pk → ∀ coins →
      ValidCiphertext (proj₁ (encapsulate pk coins))

    GeneratedAgreement : KeyGenSeed → EncapsCoins → Set

    generatedAgreementImpliesKeyEquality :
      ∀ {seed coins} → GeneratedAgreement seed coins →
      let pair = keyGen seed in
      let result = encapsulate (proj₁ pair) coins in
      decapsulate (proj₂ pair) (proj₁ result) ≡ proj₂ result

open KEMStateMachine public

record TotalGeneratedAgreement (machine : KEMStateMachine) : Set₁ where
  constructor totalGeneratedAgreement
  field
    everyGeneratedTraceAgrees :
      ∀ seed coins → GeneratedAgreement machine seed coins

open TotalGeneratedAgreement public

record GeneratedAgreementFailure (machine : KEMStateMachine) : Set₁ where
  constructor generatedAgreementFailure
  field
    seed : KeyGenSeed machine
    coins : EncapsCoins machine
    generatedKeysDiffer :
      let pair = keyGen machine seed in
      let result = encapsulate machine (proj₁ pair) coins in
      decapsulate machine (proj₂ pair) (proj₁ result) ≡ proj₂ result → ⊥

open GeneratedAgreementFailure public

------------------------------------------------------------------------
-- Decapsulation-route state.
--
-- FIPS 203 ML-KEM decapsulation internally distinguishes a valid route from
-- implicit rejection, but still returns a shared-secret value.  Whether that
-- internal route becomes externally observable is a separate protocol / system
-- property and therefore an explicit field rather than an implementation fact.
------------------------------------------------------------------------

data DecapsulationRoute : Set where
  validRoute implicitRejectRoute : DecapsulationRoute

record RoutedDecapsulation (machine : KEMStateMachine) : Set₁ where
  constructor routedDecapsulation
  field
    route : SecretKey machine → Ciphertext machine → DecapsulationRoute
    routedSecret : SecretKey machine → Ciphertext machine → SharedSecret machine
    routedSecretAgreesWithMachine :
      ∀ sk ct → routedSecret sk ct ≡ decapsulate machine sk ct

open RoutedDecapsulation public

------------------------------------------------------------------------
-- Candidate-key testing.
--
-- In an LWE-shaped public key, a candidate secret induces a residual.  Public
-- algebra may make "is this candidate structurally plausible?" inexpensive
-- even when finding a good candidate is difficult.  Verification and search
-- are intentionally separated here.
------------------------------------------------------------------------

record CandidateKeyTest : Set₁ where
  constructor candidateKeyTest
  field
    PublicState CandidateSecret Residual : Set
    residual : PublicState → CandidateSecret → Residual
    PlausibleResidual : Residual → Set

  candidatePlausible : PublicState → CandidateSecret → Set
  candidatePlausible public candidate = PlausibleResidual (residual public candidate)

open CandidateKeyTest public

record ExactCandidateWitness (test : CandidateKeyTest) : Set₁ where
  constructor exactCandidateWitness
  field
    public : PublicState test
    candidate : CandidateSecret test
    residualWitness : PlausibleResidual test (residual test public candidate)

open ExactCandidateWitness public

------------------------------------------------------------------------
-- Key confirmation is a post-KEM agreement test, not additional entropy.
-- It certifies that two derived key states agree relative to a confirmation
-- mechanism; it does not by itself establish KEM hardness.
------------------------------------------------------------------------

record KeyConfirmationContract : Set₁ where
  constructor keyConfirmationContract
  field
    SharedSecret ConfirmationKey Context Tag : Set
    deriveConfirmationKey : SharedSecret → ConfirmationKey
    tag : ConfirmationKey → Context → Tag
    verifies : ConfirmationKey → Context → Tag → Set
    selfConfirmation :
      ∀ secret context →
      verifies
        (deriveConfirmationKey secret)
        context
        (tag (deriveConfirmationKey secret) context)

open KeyConfirmationContract public
