module DASHI.Arithmetic.FiniteTwinSieveNoPromotionExact where

------------------------------------------------------------------------
-- FINITE-SIEVE CLAIM-AUTHORITY BOUNDARY
--
-- Original number theory: Eratosthenes, Brun and finite sieve methods.
-- Existing DASHI proof owners:
--   CertifiedPrimePairModulusExact (arithmetic AllPairSurvive)
--   FiniteTwinSieveUniversalCompositeBaselineExact
--     (for every N and every finite axis list, construct a surviving
--      pair with both genuine stdlib Composite certificates)
--   TwinPrimeSixWheelExact (genuine two-Prime arithmetic predicate)
--   Data.Nat.Primality (Composite -> not Prime).
--
-- New direct consumer consequence: a fixed finite prime-pair sieve
-- can never imply TwinPrimeAt on ALL surviving inputs, even when the
-- candidate must exceed an arbitrary lower bound.
--
-- This is not the Selberg/Polymath analytic parity theorem; it is an
-- elementary, constructive finite-local-observation obstruction.
-- No Monster 3B/4B or signed SSP address is promoted into a prime
-- distribution theorem. Source written; Agda kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Empty using (⊥)
import Data.Nat.Primality as Prime

import DASHI.Arithmetic.CertifiedPrimePairModulusExact as Pair
import DASHI.Arithmetic.FiniteTwinSieveUniversalCompositeBaselineExact as Composite
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin

-- An accepted finite-sieve pair can be proven NONPRIME at BOTH
-- endpoints, not merely "not yet certified prime".
arbitrarilyLargeFiniteSieveFalsePositives :
  (axes : List Pair.CertifiedPrimeAxis) →
  (N : Nat) →
  Σ Nat (λ n →
    N ≤ n
    × (Pair.AllPairSurvive axes n
      × ((Prime.Prime n → ⊥)
        × (Prime.Prime (n + 2) → ⊥))))
arbitrarilyLargeFiniteSieveFalsePositives axes N
  with Composite.everyFinitePrimeSieveHasLargeDoubleCompositeSurvivor
    axes N
... | n , (large , (survivor , (leftComposite , rightComposite))) =
  n ,
  ( large
  , ( survivor
    , ( Prime.composite⇒¬prime leftComposite
      , Prime.composite⇒¬prime rightComposite
      )
    )
  )

-- The exact arithmetic twin predicate is built from two actual
-- Prime certificates. Its supposed derivation from finite-sieve
-- survival is refuted by the constructed counterexample.
noFiniteSieveCanCertifyEveryTwin :
  (axes : List Pair.CertifiedPrimeAxis) →
  ((n : Nat) →
    Pair.AllPairSurvive axes n →
    Twin.TwinPrimeAt n) →
  ⊥
noFiniteSieveCanCertifyEveryTwin axes assumedSound
  with arbitrarilyLargeFiniteSieveFalsePositives axes 0
... | n , (bound , (survivor , (notLeft , notRight))) =
  notLeft (proj₁ (assumedSound n survivor))

-- Stronger: the same invalid promotion fails beyond EVERY bound.
noFiniteSieveCanCertifyAllLargeTwins :
  (axes : List Pair.CertifiedPrimeAxis) →
  (N : Nat) →
  ((n : Nat) →
    N ≤ n →
    Pair.AllPairSurvive axes n →
    Twin.TwinPrimeAt n) →
  ⊥
noFiniteSieveCanCertifyAllLargeTwins axes N assumedSound
  with arbitrarilyLargeFiniteSieveFalsePositives axes N
... | n , (bound , (survivor , (notLeft , notRight))) =
  notLeft (proj₁ (assumedSound n bound survivor))
