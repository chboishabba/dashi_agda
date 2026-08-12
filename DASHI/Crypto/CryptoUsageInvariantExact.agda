module DASHI.Crypto.CryptoUsageInvariantExact where

------------------------------------------------------------------------
-- REUSABLE CRYPTOGRAPHIC USAGE INVARIANTS
--
-- These are state-contract obligations shared by several primitives.  They are
-- deliberately independent of implementation leakage and of any one concrete
-- algorithm.
--
-- References:
-- Claude E. Shannon, "Communication Theory of Secrecy Systems",
-- Bell System Technical Journal 28(4), 1949.
-- DOI: 10.1002/j.1538-7305.1949.tb00928.x.
--
-- Morris Dworkin, "Recommendation for Block Cipher Modes of Operation:
-- Galois/Counter Mode (GCM) and GMAC", NIST SP 800-38D, 2007.
-- DOI: 10.6028/NIST.SP.800-38D.
--
-- Yoav Nir and Adam Langley, "ChaCha20 and Poly1305 for IETF Protocols",
-- RFC 8439, 2018. DOI: 10.17487/RFC8439.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Unique-use token.  The same mathematical pattern covers OTP pad reuse,
-- AEAD nonce reuse under one key, and fresh ephemeral randomness requirements.
------------------------------------------------------------------------

record TwoUseUniqueToken : Set₁ where
  constructor twoUseUniqueToken
  field
    Token : Set
    first second : Token
    distinct : first ≡ second → ⊥

open TwoUseUniqueToken public

record TwoUseReuseWitness (unique : TwoUseUniqueToken) : Set where
  constructor twoUseReuseWitness
  field
    reused : first unique ≡ second unique

open TwoUseReuseWitness public

reuseContradictsUniqueness :
  ∀ {unique} →
  TwoUseReuseWitness unique → ⊥
reuseContradictsUniqueness {unique} witness =
  distinct unique (reused witness)

------------------------------------------------------------------------
-- Context binding.  A protected value can be correct locally while still being
-- attached to the wrong session/context.  Binding is therefore a separate
-- invariant rather than folded into primitive correctness.
------------------------------------------------------------------------

record ContextBoundValue : Set₁ where
  constructor contextBoundValue
  field
    Context Value Bound : Set
    bind : Context → Value → Bound

open ContextBoundValue public

record ContextSwapWitness (system : ContextBoundValue) : Set where
  constructor contextSwapWitness
  field
    firstContext secondContext : Context system
    value : Value system
    contextsDiffer : firstContext ≡ secondContext → ⊥
    bindingCollides :
      bind system firstContext value ≡ bind system secondContext value

open ContextSwapWitness public

------------------------------------------------------------------------
-- Authenticated classical-channel precondition for QKD-style protocols.
------------------------------------------------------------------------

data ClassicalChannelState : Set where
  authenticated unauthenticated : ClassicalChannelState

data QKDClassicalChannelReady : ClassicalChannelState → Set where
  authenticatedReady : QKDClassicalChannelReady authenticated

unauthenticatedChannelNotQKDReady :
  QKDClassicalChannelReady unauthenticated → ⊥
unauthenticatedChannelNotQKDReady ()
