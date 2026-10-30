module DASHI.Arithmetic.SignedSSPBidirectionalNeighbourExact where

------------------------------------------------------------------------
-- SOURCES AND OWNERSHIP
--
-- John H. Conway (1987) and Richard K. Guy (1983) own historical
-- FRACTRAN prime-program prior art, not this signed arithmetic bridge.
-- Existing DASHI owners:
--   SignedSSPPrimeOffsetMacroExact (two actual guarded fraction steps);
--   SignedSSPProofCarryingExponentExact (lossless arithmetic residual);
--   SignedSSPCertifiedCRTReadoutSquareExact (positive offset CRT square);
--   CertifiedPrimePairModulusExact (arbitrary certified prime axes);
--   TwinPrimeSixWheelExact (actual arithmetic twin-prime predicate).
--
-- NEW: complete the *negative* offset modular square, plus/minus
-- decoded inverse laws, and two-way transport of prime certificates
-- starting from the UPPER endpoint of a twin pair.
--
-- This is an exact algebraic/finite-CRT bridge on CertifiedExponentCode.
-- It is not the full FRACDASH signed source→target compiler, a proof
-- of universal emission reachability, or twin-prime infinitude.
-- Agda source written; pinned-kernel acceptance not established.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_%_)
open import Data.Nat.Primality using (Prime)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans; sym)

import DASHI.Arithmetic.SignedSSPPrimeOffsetMacroExact as Offset
import DASHI.Arithmetic.SignedSSPProofCarryingExponentExact as Code
import DASHI.Arithmetic.CertifiedPrimePairModulusExact as Pair
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin

-- Every +2 output is a valid input for a guarded -2 macro.
plusCodeIsMinusAdmissible :
  (code : Code.CertifiedExponentCode) →
  Code.decodeExponent (Code.plusTwoCode code)
    ≡ suc (suc (Code.decodeExponent code))
plusCodeIsMinusAdmissible code =
  trans
    (Code.plusTwoCodeDecodesCorrectly code)
    (+-comm (Code.decodeExponent code) Offset.two)

-- The minus path consumes the actual input code rather than silently
-- creating an unrelated p-2 state with no original-exponent witness.
plusThenMinusDecodedIdentity :
  (code : Code.CertifiedExponentCode) →
  Code.decodeExponent
    (Code.minusTwoCode
      (Code.plusTwoCode code)
      (Code.decodeExponent code)
      (plusCodeIsMinusAdmissible code))
    ≡ Code.decodeExponent code
plusThenMinusDecodedIdentity code =
  Code.minusTwoCodeDecodesCorrectly
    (Code.plusTwoCode code)
    (Code.decodeExponent code)
    (plusCodeIsMinusAdmissible code)

-- Conversely, start with a genuine p=2+k, apply the guarded -2
-- macro, then +2; the decoded integer recovers the original p.
minusThenPlusDecodedIdentity :
  (k : Nat) →
  Code.decodeExponent
    (Code.plusTwoCode
      (Code.minusTwoCode (Code.encodeExponent (suc (suc k))) k refl))
    ≡ suc (suc k)
minusThenPlusDecodedIdentity k =
  +-comm k Offset.two

-- The left-neighbour CRT square, still using the DECODED exponent,
-- not the raw power-of-two integer. Includes modulus 2 exactly.
minusTwoCRTReadoutCommutes :
  (axis : Pair.CertifiedPrimeAxis) →
  (code : Code.CertifiedExponentCode) →
  (k : Nat) →
  (admissible : Code.decodeExponent code ≡ suc (suc k)) →
  (Code.decodeExponent (Code.minusTwoCode code k admissible))
    % Pair.primeModulus axis
    ≡ k % Pair.primeModulus axis
minusTwoCRTReadoutCommutes axis code k admissible =
  cong
    (λ n → n % Pair.primeModulus axis)
    (Code.minusTwoCodeDecodesCorrectly code k admissible)

-- This two-way transport works with ANY finite list of certified axes,
-- without pretending that finite sieve survival means primality.
minusTwoPairSieveTransport :
  (axes : List Pair.CertifiedPrimeAxis) →
  (code : Code.CertifiedExponentCode) →
  (k : Nat) →
  (admissible : Code.decodeExponent code ≡ suc (suc k)) →
  Pair.AllPairSurvive axes k →
  Pair.AllPairSurvive axes
    (Code.decodeExponent (Code.minusTwoCode code k admissible))
minusTwoPairSieveTransport axes code k admissible =
  subst (Pair.AllPairSurvive axes)
    (sym (Code.minusTwoCodeDecodesCorrectly code k admissible))

minusTwoPairSieveTransportBack :
  (axes : List Pair.CertifiedPrimeAxis) →
  (code : Code.CertifiedExponentCode) →
  (k : Nat) →
  (admissible : Code.decodeExponent code ≡ suc (suc k)) →
  Pair.AllPairSurvive axes
    (Code.decodeExponent (Code.minusTwoCode code k admissible)) →
  Pair.AllPairSurvive axes k
minusTwoPairSieveTransportBack axes code k admissible =
  subst (Pair.AllPairSurvive axes)
    (Code.minusTwoCodeDecodesCorrectly code k admissible)

-- Given a positive prime-certificate pair at the lower endpoint,
-- transport BOTH real arithmetic certificates to the machine's
-- upper p=k+2 code and its guarded negative-offset output.
twinAtLowerToCertifiedUpperAndMinus :
  (code : Code.CertifiedExponentCode) →
  (k : Nat) →
  (admissible : Code.decodeExponent code ≡ suc (suc k)) →
  Twin.TwinPrimeAt k →
  Prime (Code.decodeExponent (Code.minusTwoCode code k admissible))
    × Prime (Code.decodeExponent code)
twinAtLowerToCertifiedUpperAndMinus code k admissible (lower , upper) =
  subst Prime
    (sym (Code.minusTwoCodeDecodesCorrectly code k admissible))
    lower
  ,
  subst Prime (sym (trans admissible (sym (+-comm k Offset.two))))
    upper

-- The converse cannot be constructed from offset arithmetic alone.
-- It requires independently supplied Prime proofs at BOTH endpoints.
certifiedUpperAndMinusToTwinAtLower :
  (code : Code.CertifiedExponentCode) →
  (k : Nat) →
  (admissible : Code.decodeExponent code ≡ suc (suc k)) →
  Prime (Code.decodeExponent (Code.minusTwoCode code k admissible))
    × Prime (Code.decodeExponent code) →
  Twin.TwinPrimeAt k
certifiedUpperAndMinusToTwinAtLower code k admissible (lower , upper) =
  subst Prime
    (Code.minusTwoCodeDecodesCorrectly code k admissible)
    lower
  ,
  subst Prime (trans admissible (sym (+-comm k Offset.two)))
    upper
