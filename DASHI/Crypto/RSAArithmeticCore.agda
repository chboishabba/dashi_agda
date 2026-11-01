module DASHI.Crypto.RSAArithmeticCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.Base369Nat using (NonZero; _%_)
open import DASHI.Arithmetic.DeltaGrowth using (pow)

------------------------------------------------------------------------
-- RSA arithmetic core.
--
-- This module stays on the Nat surface and remains fail-closed:
--   * key/state records are concrete and explicit,
--   * residue records are explicit Nat carriers,
--   * modular equality is represented as a symbolic remainder equality,
--   * encryption is a Nat-level powMod surface,
--   * decryption is only packaged as a candidate boundary, not as a theorem.

powMod :
  (base exponent modulus : Nat) →
  .{{_ : NonZero modulus}} →
  Nat
powMod base exponent modulus = pow base exponent % modulus

record ModEq (modulus left right : Nat) : Set where
  constructor mkModEq
  field
    leftRemainder :
      Nat

    rightRemainder :
      Nat

    remaindersEqual :
      leftRemainder ≡ rightRemainder

open ModEq public

reflModEq :
  ∀ {modulus left} →
  ModEq modulus left left
reflModEq {left = left} =
  mkModEq
    left
    left
    refl

------------------------------------------------------------------------
-- RSA key state.

record RSAPublicState : Set where
  constructor mkRSAPublicState
  field
    publicModulus :
      Nat

    publicModulusWitness :
      NonZero publicModulus

    publicExponent :
      Nat

    publicStateCandidate :
      Bool

    publicStateCandidateIsFalse :
      publicStateCandidate ≡ false

open RSAPublicState public

record RSAPrivateState : Set where
  constructor mkRSAPrivateState
  field
    privateModulus :
      Nat

    privateModulusWitness :
      NonZero privateModulus

    privatePublicExponent :
      Nat

    privatePrivateExponent :
      Nat

    privateStateCandidate :
      Bool

    privateStateCandidateIsFalse :
      privateStateCandidate ≡ false

open RSAPrivateState public

rsaPublicProjection :
  RSAPrivateState →
  RSAPublicState
rsaPublicProjection privateState =
  mkRSAPublicState
    (privateModulus privateState)
    (privateModulusWitness privateState)
    (privatePublicExponent privateState)
    false
    refl

record ValidRSAKey : Set where
  constructor mkValidRSAKey
  field
    validPrivateState :
      RSAPrivateState

    validPublicState :
      RSAPublicState

    validPublicProjection :
      rsaPublicProjection validPrivateState ≡ validPublicState

    validKeyCandidate :
      Bool

    validKeyCandidateIsFalse :
      validKeyCandidate ≡ false

open ValidRSAKey public

------------------------------------------------------------------------
-- Residue carriers.

record RSAPlainResidue (modulus : Nat) : Set where
  constructor mkRSAPlainResidue
  field
    plainValue :
      Nat

    plainValueModEq :
      ModEq modulus plainValue plainValue

    plainResidueCandidate :
      Bool

    plainResidueCandidateIsFalse :
      plainResidueCandidate ≡ false

open RSAPlainResidue public

record RSACipherResidue (modulus : Nat) : Set where
  constructor mkRSACipherResidue
  field
    cipherValue :
      Nat

    cipherValueModEq :
      ModEq modulus cipherValue cipherValue

    cipherResidueCandidate :
      Bool

    cipherResidueCandidateIsFalse :
      cipherResidueCandidate ≡ false

open RSACipherResidue public

------------------------------------------------------------------------
-- RSA residue transforms.

rsaEncryptResidue :
  (publicState : RSAPublicState) →
  RSAPlainResidue (publicModulus publicState) →
  RSACipherResidue (publicModulus publicState)
rsaEncryptResidue publicState plainResidue =
  mkRSACipherResidue
    (powMod
      (plainValue plainResidue)
      (publicExponent publicState)
      (publicModulus publicState)
      {{publicModulusWitness publicState}})
    (reflModEq
      {modulus = publicModulus publicState}
      {left = powMod
        (plainValue plainResidue)
        (publicExponent publicState)
        (publicModulus publicState)
        {{publicModulusWitness publicState}}})
    false
    refl

------------------------------------------------------------------------
-- Candidate round-trip boundary.
--
-- This is intentionally not a theorem that RSA decryption inverts
-- encryption.  It records the boundary shape and a caller-supplied residue
-- equality witness, while keeping the authority lane blocked.

record RSADecryptCandidateRoundTripBoundary : Set where
  constructor mkRSADecryptCandidateRoundTripBoundary
  field
    boundaryPublicState :
      RSAPublicState

    boundaryPlainResidue :
      RSAPlainResidue (publicModulus boundaryPublicState)

    boundaryCipherResidue :
      RSACipherResidue (publicModulus boundaryPublicState)

    boundaryRecoveredResidue :
      RSAPlainResidue (publicModulus boundaryPublicState)

    boundaryRoundTripModEq :
      ModEq
        (publicModulus boundaryPublicState)
        (plainValue boundaryPlainResidue)
        (plainValue boundaryRecoveredResidue)

    boundaryCandidate :
      Bool

    boundaryCandidateIsFalse :
      boundaryCandidate ≡ false

open RSADecryptCandidateRoundTripBoundary public

rsaDecryptCandidateRoundTripBoundary :
  (key : ValidRSAKey) →
  (plainResidue :
    RSAPlainResidue (publicModulus (validPublicState key))) →
  (recoveredResidue :
    RSAPlainResidue (publicModulus (validPublicState key))) →
  ModEq
    (publicModulus (validPublicState key))
    (plainValue plainResidue)
    (plainValue recoveredResidue) →
  RSADecryptCandidateRoundTripBoundary
rsaDecryptCandidateRoundTripBoundary key plainResidue recoveredResidue roundTripModEq =
  mkRSADecryptCandidateRoundTripBoundary
    (validPublicState key)
    plainResidue
    (rsaEncryptResidue (validPublicState key) plainResidue)
    recoveredResidue
    roundTripModEq
    false
    refl

------------------------------------------------------------------------
-- Packaged surface.

record RSAArithmeticCoreSurface : Set₁ where
  field
    powSurface :
      Nat →
      Nat →
      Nat

    powModSurface :
      (base exponent modulus : Nat) →
      .{{_ : NonZero modulus}} →
      Nat

    modEqSurface :
      (modulus left right : Nat) →
      Set

    publicProjectionSurface :
      RSAPrivateState →
      RSAPublicState

    encryptResidueSurface :
      (publicState : RSAPublicState) →
      RSAPlainResidue (publicModulus publicState) →
      RSACipherResidue (publicModulus publicState)

    roundTripBoundarySurface :
      RSADecryptCandidateRoundTripBoundary →
      Bool

open RSAArithmeticCoreSurface public

rsaArithmeticCoreSurface : RSAArithmeticCoreSurface
rsaArithmeticCoreSurface = record
  { powSurface = pow
  ; powModSurface = powMod
  ; modEqSurface = ModEq
  ; publicProjectionSurface = rsaPublicProjection
  ; encryptResidueSurface = rsaEncryptResidue
  ; roundTripBoundarySurface = λ _ → false
  }
