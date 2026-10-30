module DASHI.Arithmetic.SignedSSPProofCarryingExponentExact where

------------------------------------------------------------------------
-- SOURCE AND CLAIM AUTHORITY
--
-- DASHI.Biology.SignedSSPFRACTRANWeaveExact owns typed SSP lanes and
-- signed multiplicities. The lane ssp2 is the exponent base, *not*
-- the claim that the entire set of arithmetic primes equals SSP15.
--
-- DASHI.Arithmetic.SignedSSPPrimeOffsetMacroExact owns actual two-step
-- FRACTRAN fraction-guard certificates for +2/-2 exponent updates.
--
-- DASHI.Combinatorics.SSP15FractranCompression owns the concept of an
-- SSP label PLUS sufficient residual to preserve exact arithmetic.
--
-- New concrete dependent arithmetic code (not an implementation of
-- the full EV5/FRACDASH runtime): carry the exponent p as a typed
-- residual and prove that the payload is exactly 2^p. The decoder
-- reads the certified exponent, never the raw FRACTRAN integer modulo p.
--
-- No claim of a universal signed SSP FRACTRAN prime emitter, analytic
-- prime distribution theorem, or Monster representation identity.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Arithmetic.SignedSSPPrimeOffsetMacroExact as Offset

record CertifiedExponentCode : Set where
  constructor certifiedExponentCode
  field
    carrierLane : Signed.SSPPrime
    signedMagnitude : Signed.SignedMultiplicity
    exponentResidual : Nat
    rawIntegerCode : Nat
    carrierIsTwo : carrierLane ≡ Signed.ssp2
    payloadIsPowerTwo :
      rawIntegerCode ≡ Offset.powerTwo exponentResidual

open CertifiedExponentCode public

-- This is a real, concrete code over the existing ssp2 carrier. It is
-- NOT a proof that the machine reaches the code by executing from its
-- initial state, nor that n is prime.
encodeExponent : Nat → CertifiedExponentCode
encodeExponent n =
  certifiedExponentCode
    Signed.ssp2
    (Signed.positiveMultiplicity n)
    n
    (Offset.powerTwo n)
    refl
    refl

decodeExponent : CertifiedExponentCode → Nat
decodeExponent = exponentResidual

decodeEncodeExponent :
  (n : Nat) →
  decodeExponent (encodeExponent n) ≡ n
decodeEncodeExponent n = refl

encodeUsesSSPBaseTwo :
  (n : Nat) →
  carrierLane (encodeExponent n) ≡ Signed.ssp2
encodeUsesSSPBaseTwo n = refl

encodeIsPositiveSigned :
  (n : Nat) →
  Signed.orientationOfMultiplicity (signedMagnitude (encodeExponent n))
    ≡ Signed.forwardOrientation
encodeIsPositiveSigned n = refl

-- Every accepted arbitrary code has a certified arithmetic readout.
-- For a malformed raw code to be accepted, it would need a false
-- equality proof; merely having an SSP label cannot certify it.
payloadMatchesDecodedExponent :
  (code : CertifiedExponentCode) →
  rawIntegerCode code ≡ Offset.powerTwo (decodeExponent code)
payloadMatchesDecodedExponent = payloadIsPowerTwo

-- The FRACTRAN +2 macro starts at 9*2^n and ends at 2^(n+2).
-- The payload can be substituted for 2^n ONLY through the proof.
plusMacroSourceMatchesCertifiedCode :
  (code : CertifiedExponentCode) →
  9 * rawIntegerCode code ≡ Offset.plusSource (decodeExponent code)
plusMacroSourceMatchesCertifiedCode code =
  cong (λ x → 9 * x) (payloadIsPowerTwo code)

-- Concrete result of executing the +2 FRACTRAN macro on the certified
-- code's arithmetic exponent. The raw output is the real macro output.
plusTwoCode : CertifiedExponentCode → CertifiedExponentCode
plusTwoCode code =
  certifiedExponentCode
    Signed.ssp2
    (Signed.positiveMultiplicity (decodeExponent code + Offset.two))
    (decodeExponent code + Offset.two)
    (Offset.plusOutput (decodeExponent code))
    refl
    (Offset.plusOutputHasOffsetExponent (decodeExponent code))

plusTwoCodeDecodesCorrectly :
  (code : CertifiedExponentCode) →
  decodeExponent (plusTwoCode code)
    ≡ decodeExponent code + Offset.two
plusTwoCodeDecodesCorrectly code = refl

plusTwoCodeRawIsActualMacroOutput :
  (code : CertifiedExponentCode) →
  rawIntegerCode (plusTwoCode code)
    ≡ Offset.plusOutput (decodeExponent code)
plusTwoCodeRawIsActualMacroOutput code = refl

-- The minus path is guarded by a proof of the input exponent form
-- p = 2+k. This is not a subtraction on a bare unbounded Nat.
minusTwoCodeAt : (k : Nat) → CertifiedExponentCode
minusTwoCodeAt k =
  certifiedExponentCode
    Signed.ssp2
    (Signed.positiveMultiplicity k)
    k
    (Offset.minusOutput k)
    refl refl

minusTwoCodeAtDecodesCorrectly :
  (k : Nat) →
  decodeExponent (minusTwoCodeAt k) ≡ k
minusTwoCodeAtDecodesCorrectly k = refl

minusMacroStartsAtEncodedExponent :
  (k : Nat) →
  Offset.minusSource k ≡
    9 * rawIntegerCode (encodeExponent (suc (suc k)))
minusMacroStartsAtEncodedExponent k =
  Offset.minusStartIsPrimeEncoded k

minusTwoCodeRawIsActualMacroOutput :
  (k : Nat) →
  rawIntegerCode (minusTwoCodeAt k)
    ≡ Offset.minusOutput k
minusTwoCodeRawIsActualMacroOutput k = refl

-- The exponent is recoverable, not a many-to-one sign-only label.
encodeExponentInjective :
  (p q : Nat) →
  encodeExponent p ≡ encodeExponent q →
  p ≡ q
encodeExponentInjective p q equalCodes =
  trans
    (sym (decodeEncodeExponent p))
    (trans
      (cong decodeExponent equalCodes)
      (decodeEncodeExponent q))

-- A real certified input code for p=2+k yields the guarded minus macro.
-- The source-comparison lemma explicitly uses the payload equality,
-- preventing raw-code/modulus confusion.
minusMacroSourceMatchesCertifiedCode :
  (code : CertifiedExponentCode) →
  (k : Nat) →
  decodeExponent code ≡ suc (suc k) →
  9 * rawIntegerCode code ≡ Offset.minusSource k
minusMacroSourceMatchesCertifiedCode code k originalExponent =
  trans
    (plusMacroSourceMatchesCertifiedCode code)
    (trans
      (cong Offset.plusSource originalExponent)
      (sym (Offset.minusStartIsPrimeEncoded k)))

minusTwoCode :
  (code : CertifiedExponentCode) →
  (k : Nat) →
  decodeExponent code ≡ suc (suc k) →
  CertifiedExponentCode
minusTwoCode code k originalExponent = minusTwoCodeAt k

minusTwoCodeDecodesCorrectly :
  (code : CertifiedExponentCode) →
  (k : Nat) →
  (originalExponent : decodeExponent code ≡ suc (suc k)) →
  decodeExponent (minusTwoCode code k originalExponent) ≡ k
minusTwoCodeDecodesCorrectly code k originalExponent = refl
