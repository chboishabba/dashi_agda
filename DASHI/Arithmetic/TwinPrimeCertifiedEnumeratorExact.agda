module DASHI.Arithmetic.TwinPrimeCertifiedEnumeratorExact where

------------------------------------------------------------------------
-- SOURCE AUTHORITY
-- Reuses proof-bearing arithmetic primality:
--   DASHI.Analysis.NatPrimeCountingInstance (Nat prime decider);
--   DASHI.Analysis.PrimeCountingFunction (generic exact counting and list);
--   DASHI.Arithmetic.TwinPrimeSixWheelExact (canonical TwinPrimeAt).
--
-- Classical prime-pair source roots: Brun (1919), Hardy--Littlewood (1923).
-- New DASHI owner: fully proof-bearing twin-start decider, its exact
-- finite count/list, and cardinality theorem via the existing generic
-- counting implementation. This is a FINITE enumeration theorem, NOT
-- a twin-infinitude theorem and not a claim that the signed SSP machine
-- reaches each accepted output. Every status remains kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat.Primality as NatPrimality using (Prime; prime?)

import DASHI.Analysis.PrimeCountingFunction as Generic
import DASHI.Analysis.NatPrimeCountingInstance as NatCounter
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin

-- Every Nat, including 0,1,2,3, is decided using true arithmetic
-- prime certificates, rather than a fixed SSP15 or six-wheel screen.
twinPrimeAt? : (n : Nat) → Dec (Twin.TwinPrimeAt n)
twinPrimeAt? n
  with NatPrimality.prime? n
     | NatPrimality.prime? (n + Twin.two)
... | yes left | yes right = yes (left , right)
... | no notLeft | _ =
  no (λ pair → notLeft (proj₁ pair))
... | yes left | no notRight =
  no (λ pair → notRight (proj₂ pair))

-- Borrow all finite recursion and cardinality proof from the existing
-- generic PrimeCountingFunction owner; this is a different predicate
-- instantiated in its proof-bearing counting interface.
twinStartPredicate : Generic.PrimePredicate
twinStartPredicate = record
  { Prime = Twin.TwinPrimeAt
  ; prime? = twinPrimeAt?
  }

twinStartsUpTo : Nat → List Nat
twinStartsUpTo = Generic.primesUpTo twinStartPredicate

twinPairCountLE : Nat → Nat
twinPairCountLE = Generic.primeCountLE twinStartPredicate

twinPairCountSymmetricTwice : Nat → Nat
twinPairCountSymmetricTwice =
  Generic.primeCountSymmetricTwice twinStartPredicate

twinPairIndicator : Nat → Nat
twinPairIndicator = Generic.primeIndicator twinStartPredicate

-- The result counts genuine certified pairs, not CRT survivors.
twinStartListCountExact :
  (limit : Nat) →
  Generic.listLength (twinStartsUpTo limit)
    ≡ twinPairCountLE limit
twinStartListCountExact =
  Generic.primeListCountExact twinStartPredicate

twinCountStep :
  (n : Nat) →
  twinPairCountLE (suc (suc n))
    ≡ twinPairIndicator (suc (suc n))
      + twinPairCountLE (suc n)
twinCountStep =
  Generic.primeCountStep twinStartPredicate

-- A +2 macro output is a prime neighbour exactly when this actual
-- decider returns a certificate. The macro's exact exponent readout
-- is owned by SignedSSPPrimeOffsetMacroExact and not duplicated here.
certifiedTwinFromSeparatePrimeProofs :
  (n : Nat) →
  Prime n →
  Prime (n + Twin.two) →
  Twin.TwinPrimeAt n
certifiedTwinFromSeparatePrimeProofs n left right = left , right

-- The inverse projection shows a true pair retains BOTH independent
-- original mathematical primality proofs. A signed register tag alone
-- can provide neither of them.
certifiedTwinProvidesBothPrimes :
  (n : Nat) →
  Twin.TwinPrimeAt n →
  Prime n × Prime (n + Twin.two)
certifiedTwinProvidesBothPrimes n pair = pair
