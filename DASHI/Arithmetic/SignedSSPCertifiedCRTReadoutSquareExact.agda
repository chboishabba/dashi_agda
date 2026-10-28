module DASHI.Arithmetic.SignedSSPCertifiedCRTReadoutSquareExact where

------------------------------------------------------------------------
-- SOURCE / ATTRIBUTION
--
-- Arithmetic local CRT/sieve: classical Chinese remainder theorem,
-- Eratosthenes/Brun; repository owner CertifiedPrimePairModulusExact.
-- Certified twin predicate: TwinPrimeSixWheelExact.
-- Signed SSP arithmetic compiler: SignedSSPProofCarryingExponentExact;
-- exact fraction +/-2 macro: SignedSSPPrimeOffsetMacroExact.
--
-- NEW CONCRETE COMMUTING SQUARE on the proof-carrying *arithmetic*
-- exponent code, not the raw FRACTRAN integer:
--
--     signed SSP certified 2^p  --[2/3 twice]--> certified 2^(p+2)
--              | decode p                        | decode p+2
--              v                                 v
--              p  ------------------------------> p+2
--                   reduce either value modulo ANY certified axis
--
-- This proves the local-modulus +2 square and transports real prime
-- certificates in both directions. It does NOT supply a general
-- CRT inverse or prove the real FRACDASH interpreter reaches these
-- codes from its initial state. No analytic prime-gap claim follows.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (_%_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.Primality using (Prime)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym)

import DASHI.Arithmetic.CertifiedPrimePairModulusExact as CRT
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin
import DASHI.Arithmetic.SignedSSPPrimeOffsetMacroExact as Offset
import DASHI.Arithmetic.SignedSSPProofCarryingExponentExact as Code

-- Exact residue commutation on the correctly decoded arithmetic value.
-- The raw payload 2^(p+2) must NOT be reduced in place of p+2.
plusTwoCRTReadoutCommutes :
  (axis : CRT.CertifiedPrimeAxis) →
  (code : Code.CertifiedExponentCode) →
  (Code.decodeExponent (Code.plusTwoCode code))
    % CRT.primeModulus axis
  ≡
  (Code.decodeExponent code + Offset.two)
    % CRT.primeModulus axis
plusTwoCRTReadoutCommutes axis code =
  cong
    (λ n → n % CRT.primeModulus axis)
    (Code.plusTwoCodeDecodesCorrectly code)

-- The same exact commuting square works over any finite list of
-- certified prime axes without assuming a general CRT inverse.
pairSieveTransportThroughPlusCode :
  (axes : List CRT.CertifiedPrimeAxis) →
  (code : Code.CertifiedExponentCode) →
  CRT.AllPairSurvive axes (Code.decodeExponent code + Offset.two) →
  CRT.AllPairSurvive axes (Code.decodeExponent (Code.plusTwoCode code))
pairSieveTransportThroughPlusCode axes code =
  subst (CRT.AllPairSurvive axes)
    (sym (Code.plusTwoCodeDecodesCorrectly code))

pairSieveTransportThroughPlusCodeBack :
  (axes : List CRT.CertifiedPrimeAxis) →
  (code : Code.CertifiedExponentCode) →
  CRT.AllPairSurvive axes (Code.decodeExponent (Code.plusTwoCode code)) →
  CRT.AllPairSurvive axes (Code.decodeExponent code + Offset.two)
pairSieveTransportThroughPlusCodeBack axes code =
  subst (CRT.AllPairSurvive axes)
    (Code.plusTwoCodeDecodesCorrectly code)

-- If the original arithmetic p and p+2 have independent prime proofs,
-- the two certified codes preserve those proofs when decoded.
twinPrimeToCertifiedCodePair :
  (code : Code.CertifiedExponentCode) →
  Twin.TwinPrimeAt (Code.decodeExponent code) →
  Prime (Code.decodeExponent code)
  × Prime (Code.decodeExponent (Code.plusTwoCode code))
twinPrimeToCertifiedCodePair code (left , right) =
  left ,
  subst Prime (sym (Code.plusTwoCodeDecodesCorrectly code)) right

certifiedCodePairToTwinPrime :
  (code : Code.CertifiedExponentCode) →
  Prime (Code.decodeExponent code)
  × Prime (Code.decodeExponent (Code.plusTwoCode code)) →
  Twin.TwinPrimeAt (Code.decodeExponent code)
certifiedCodePairToTwinPrime code (left , right) =
  left ,
  subst Prime (Code.plusTwoCodeDecodesCorrectly code) right

-- This two-way equivalence uses the source-owned true arithmetic
-- primality certificates, not the selected FRACDASH prime tag.
