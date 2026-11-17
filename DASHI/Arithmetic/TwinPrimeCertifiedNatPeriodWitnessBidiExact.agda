module DASHI.Arithmetic.TwinPrimeCertifiedNatPeriodWitnessBidiExact where

------------------------------------------------------------------------
-- Q26 + D06 + M16: REAL CERTIFIED TWIN EVIDENCE ↔ PERIOD CODE.
--
-- Strict original owner: TwinPrimeSixWheelExact.TwinPrimeAt uses
-- independent NatPrimality.Prime proofs at n and n+2.
-- Original NatPeriod270 owner supplies BOTH arithmetic inverse laws.
-- Neither residue nor Ibrahim/global antipodal class alone owns
-- the prime evidence. The actual unbounded period must survive.
--
-- This is a proof-carrying two-sided map, with both underlying
-- CODE roundtrips. It does not invoke proof irrelevance or pretend
-- that arbitrary proofs inside a dependent Sigma are definitionally
-- identical. Source-written; kernel pending. 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (sym; subst)

import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin
import DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact as Period

CertifiedNatTwin : Set
CertifiedNatTwin = Σ Nat Twin.TwinPrimeAt

CertifiedPeriodTwin : Set
CertifiedPeriodTwin =
  Σ Period.NatPeriod270
    (λ code → Twin.TwinPrimeAt (Period.decodeNatPeriod270 code))

natTwinToPeriod :
  CertifiedNatTwin → CertifiedPeriodTwin
natTwinToPeriod (n , certified) =
  Period.encodeNatPeriod270 n ,
    subst Twin.TwinPrimeAt
      (sym (Period.decodeEncodeNatPeriod270 n))
      certified

periodTwinToNat :
  CertifiedPeriodTwin → CertifiedNatTwin
periodTwinToNat (code , certified) =
  Period.decodeNatPeriod270 code , certified

natTwinRoundTripValue :
  (pair : CertifiedNatTwin) →
  proj₁ (periodTwinToNat (natTwinToPeriod pair)) ≡ proj₁ pair
natTwinRoundTripValue (n , certified) =
  Period.decodeEncodeNatPeriod270 n

periodTwinRoundTripCode :
  (pair : CertifiedPeriodTwin) →
  proj₁ (natTwinToPeriod (periodTwinToNat pair)) ≡ proj₁ pair
periodTwinRoundTripCode (code , certified) =
  Period.encodeDecodeNatPeriod270 code

-- Direct transport in both directions, with the actual prime
-- certificates retained as proofs rather than Boolean tags.
certifiedTwinToEncoded :
  (n : Nat) →
  Twin.TwinPrimeAt n →
  Twin.TwinPrimeAt
    (Period.decodeNatPeriod270 (Period.encodeNatPeriod270 n))
certifiedTwinToEncoded n =
  subst Twin.TwinPrimeAt
    (sym (Period.decodeEncodeNatPeriod270 n))

encodedTwinToCertified :
  (n : Nat) →
  Twin.TwinPrimeAt
    (Period.decodeNatPeriod270 (Period.encodeNatPeriod270 n)) →
  Twin.TwinPrimeAt n
encodedTwinToCertified n =
  subst Twin.TwinPrimeAt (Period.decodeEncodeNatPeriod270 n)
