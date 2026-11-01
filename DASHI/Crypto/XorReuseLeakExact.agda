module DASHI.Crypto.XorReuseLeakExact where

------------------------------------------------------------------------
-- EXACT XOR REUSE LEAKAGE
--
-- Concrete finite theorem shared by the one-time pad and any stream-encryption
-- abstraction in which two messages are XORed with the same keystream bit.
-- This does not assert that a conforming AES-GCM or ChaCha20-Poly1305 execution
-- reuses a nonce; nonce uniqueness is a precondition precisely to prevent such
-- repeated-keystream states.
--
-- References:
-- Claude E. Shannon, "Communication Theory of Secrecy Systems",
-- Bell System Technical Journal 28(4), 1949.
-- DOI: 10.1002/j.1538-7305.1949.tb00928.x.
--
-- Morris Dworkin, NIST SP 800-38D, GCM/GMAC.
-- DOI: 10.6028/NIST.SP.800-38D.
--
-- Yoav Nir and Adam Langley, RFC 8439, ChaCha20 and Poly1305.
-- DOI: 10.17487/RFC8439.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

xor : Bool → Bool → Bool
xor false b = b
xor true false = true
xor true true = false

xorSelfZero : ∀ b → xor b b ≡ false
xorSelfZero false = refl
xorSelfZero true = refl

xorRightZero : ∀ b → xor b false ≡ b
xorRightZero false = refl
xorRightZero true = refl

xorAssoc : ∀ a b c → xor (xor a b) c ≡ xor a (xor b c)
xorAssoc false false false = refl
xorAssoc false false true = refl
xorAssoc false true false = refl
xorAssoc false true true = refl
xorAssoc true false false = refl
xorAssoc true false true = refl
xorAssoc true true false = refl
xorAssoc true true true = refl

xorComm : ∀ a b → xor a b ≡ xor b a
xorComm false false = refl
xorComm false true = refl
xorComm true false = refl
xorComm true true = refl

-- Two ciphertext bits formed with the same pad/keystream reveal the XOR
-- relation of the plaintext bits exactly.
sameKeystreamRevealsPlaintextRelation :
  ∀ message1 message2 keystream →
  xor (xor message1 keystream) (xor message2 keystream)
  ≡ xor message1 message2
sameKeystreamRevealsPlaintextRelation false false false = refl
sameKeystreamRevealsPlaintextRelation false false true = refl
sameKeystreamRevealsPlaintextRelation false true false = refl
sameKeystreamRevealsPlaintextRelation false true true = refl
sameKeystreamRevealsPlaintextRelation true false false = refl
sameKeystreamRevealsPlaintextRelation true false true = refl
sameKeystreamRevealsPlaintextRelation true true false = refl
sameKeystreamRevealsPlaintextRelation true true true = refl

-- One-time-pad specialization: reuse destroys the intended one-use state
-- invariant even though each individual encryption equation remains correct.
otpReuseRelationLeak :
  ∀ message1 message2 pad →
  xor (xor message1 pad) (xor message2 pad)
  ≡ xor message1 message2
otpReuseRelationLeak = sameKeystreamRevealsPlaintextRelation
