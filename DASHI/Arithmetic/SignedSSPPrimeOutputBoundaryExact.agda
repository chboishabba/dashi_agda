module DASHI.Arithmetic.SignedSSPPrimeOutputBoundaryExact where

------------------------------------------------------------------------
-- Proof-authority boundary for signed SSP + FRACDASH prime-producing
-- machines, and exact readout transport to the arithmetic twin sieve.
--
-- Reuses:
--  Conway PRIMEGAME (historical theorem, no copy or impersonation);
--  SignedSSPPrimeOffsetMacroExact (source-written two-step ±2 macros);
--  TwinPrimeSixWheelExact (arithmetic TwinPrimeAt);
--  CertifiedPrimePairModulusExact (arbitrary finite arithmetic sieve);
--  FRACDASH signed compiler and first-applicable interpreter as donors.
--
-- No universal prime emission is manufactured. The required reachability
-- theorem is an explicitly UNINSTANTIATED record field. Neither signed
-- representation nor residue symmetry can create arithmetic primality.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Nat.Primality using (Prime)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Arithmetic.SignedSSPPrimeOffsetMacroExact as Offset
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin
import DASHI.Arithmetic.CertifiedPrimePairModulusExact as Pair

-- Power-of-two representability is cheap, and does not assert a machine
-- actually reaches the encoding state from its canonical initial state.
record CertifiedEncodedPrime (p : Nat) : Set where
  constructor certifiedEncodedPrime
  field
    primeProof : Prime p
    code : Nat
    codeIsPowerTwo : code ≡ Offset.powerTwo p

open CertifiedEncodedPrime public

everyCertifiedPrimeHasAnEncoding :
  (p : Nat) → Prime p → CertifiedEncodedPrime p
everyCertifiedPrimeHasAnEncoding p proof =
  certifiedEncodedPrime proof (Offset.powerTwo p) refl

-- This is the actual missing CONSTRUCTIVE-COMPLETENESS interface.
-- State and Reachable must refer to the real signed SSP executable VM.
-- An inhabitant requires a proof for EVERY arithmetic prime, not an
-- enumeration of SSP15 labels or a finite Python/Agda regression.
record ArithmeticPrimeEmitter : Set₁ where
  field
    State : Set
    initial : State
    Reachable : State → State → Set
    readout : State → Nat
    coversEveryPrime :
      (p : Nat) → Prime p →
      Σ State (λ s →
        Reachable initial s × readout s ≡ Offset.powerTwo p)

open ArithmeticPrimeEmitter public

-- Source-faithful theorem: wherever an emitter's concrete implementation
-- is supplied, the original power-of-two code can be observed in a
-- reachable state. This DOES NOT construct an instance.
certifiedPrimeIsReachableWhenEmitterProved :
  (E : ArithmeticPrimeEmitter) →
  (p : Nat) → Prime p →
  Σ (State E) (λ s →
    Reachable E (initial E) s × readout E s ≡ Offset.powerTwo p)
certifiedPrimeIsReachableWhenEmitterProved E p proof =
  coversEveryPrime E p proof

-- Exact semantic firewall: same decoded integer implies the SAME
-- arithmetic twin-primality proposition. A signed tag/phase/SSP address
-- cannot change arithmetic truth while preserving its decoder.
twinPrimeInvariantUnderEqualReadout :
  ∀ {State : Set} →
  (decode : State → Nat) →
  (x y : State) →
  decode x ≡ decode y →
  Twin.TwinPrimeAt (decode x) →
  Twin.TwinPrimeAt (decode y)
twinPrimeInvariantUnderEqualReadout decode x y same =
  subst Twin.TwinPrimeAt same

twinPrimeInvariantUnderEqualReadoutBack :
  ∀ {State : Set} →
  (decode : State → Nat) →
  (x y : State) →
  decode x ≡ decode y →
  Twin.TwinPrimeAt (decode y) →
  Twin.TwinPrimeAt (decode x)
twinPrimeInvariantUnderEqualReadoutBack decode x y same =
  subst Twin.TwinPrimeAt (sym same)

-- The same holds for the *actual* arbitrary-prime sieve, not merely an
-- SSP register-tag filter. This reuses the canonical type of survivors.
pairSieveInvariantUnderEqualReadout :
  ∀ {State : Set} →
  (axes : List Pair.CertifiedPrimeAxis) →
  (decode : State → Nat) →
  (x y : State) →
  decode x ≡ decode y →
  Pair.AllPairSurvive axes (decode x) →
  Pair.AllPairSurvive axes (decode y)
pairSieveInvariantUnderEqualReadout axes decode x y same =
  subst (Pair.AllPairSurvive axes) same

pairSieveInvariantUnderEqualReadoutBack :
  ∀ {State : Set} →
  (axes : List Pair.CertifiedPrimeAxis) →
  (decode : State → Nat) →
  (x y : State) →
  decode x ≡ decode y →
  Pair.AllPairSurvive axes (decode y) →
  Pair.AllPairSurvive axes (decode x)
pairSieveInvariantUnderEqualReadoutBack axes decode x y same =
  subst (Pair.AllPairSurvive axes) (sym same)

-- Both primality certificates remain independently required: simply
-- producing Offset.plusTwoFractionMacro does not provide the right one.
certifiedNeighboursAreTwinPrimes :
  (p : Nat) →
  Prime p →
  Prime (p + Offset.two) →
  Twin.TwinPrimeAt p
certifiedNeighboursAreTwinPrimes p left right = left , right
