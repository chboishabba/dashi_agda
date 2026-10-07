module DASHI.Core.BinaryWordIntegerChernoffExact where

------------------------------------------------------------------------
-- INTEGER CHERNOFF BOUND FOR THE COMPLETE BINARY WORD CARRIER
--
-- Weight a word by 2^(number of one-bits).  Summing over all length-m words
-- gives 3^m exactly.  Every word with at least k ones has weight at least 2^k,
-- therefore
--
--   2^k * #{w : BinaryWord m | ones(w) >= k} <= 3^m.
--
-- This is finite Nat arithmetic: no measure theory, logarithms, spectral gap,
-- or asymptotic theorem is involved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong; cong₂)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Bool.Base using (T)
open import Data.Nat using (_≤_; _≤ᵇ_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary

powNat : Nat → Nat → Nat
powNat base zero = 1
powNat base (suc n) = base * powNat base n

ones : {m : Nat} → Binary.BinaryWord m → Nat
ones Binary.end = zero
ones (Binary.bit0 tail) = ones tail
ones (Binary.bit1 tail) = suc (ones tail)

wordFold :
  {m : Nat} →
  (Binary.BinaryWord m → Nat) →
  Nat
wordFold {zero} f = f Binary.end
wordFold {suc m} f =
  wordFold (λ tail → f (Binary.bit0 tail))
  + wordFold (λ tail → f (Binary.bit1 tail))

foldMono :
  {m : Nat} →
  (f g : Binary.BinaryWord m → Nat) →
  ((word : Binary.BinaryWord m) → f word ≤ g word) →
  wordFold f ≤ wordFold g
foldMono {zero} f g pointwise = pointwise Binary.end
foldMono {suc m} f g pointwise =
  NatP.+-mono-≤
    (foldMono
      (λ tail → f (Binary.bit0 tail))
      (λ tail → g (Binary.bit0 tail))
      (λ tail → pointwise (Binary.bit0 tail)))
    (foldMono
      (λ tail → f (Binary.bit1 tail))
      (λ tail → g (Binary.bit1 tail))
      (λ tail → pointwise (Binary.bit1 tail)))

scaleFold :
  {m : Nat} →
  (scale : Nat) →
  (f : Binary.BinaryWord m → Nat) →
  scale * wordFold f
  ≡ wordFold (λ word → scale * f word)
scaleFold {zero} scale f = refl
scaleFold {suc m} scale f =
  trans
    (NatP.*-distribˡ-+ scale
      (wordFold (λ tail → f (Binary.bit0 tail)))
      (wordFold (λ tail → f (Binary.bit1 tail))))
    (cong₂ _+_
      (scaleFold scale (λ tail → f (Binary.bit0 tail)))
      (scaleFold scale (λ tail → f (Binary.bit1 tail))))

wordWeight :
  {m : Nat} →
  Binary.BinaryWord m → Nat
wordWeight word = powNat 2 (ones word)

weightedTotal : Nat → Nat
weightedTotal m = wordFold (wordWeight {m})

weightedTotalPowThree :
  (m : Nat) →
  weightedTotal m ≡ powNat 3 m
weightedTotalPowThree zero = refl
weightedTotalPowThree (suc m) =
  let
    total = weightedTotal m

    zeroHalf :
      wordFold (λ tail → wordWeight (Binary.bit0 tail)) ≡ total
    zeroHalf = refl

    oneHalf :
      wordFold (λ tail → wordWeight (Binary.bit1 tail)) ≡ 2 * total
    oneHalf = sym (scaleFold 2 (wordWeight {m}))

    combine : total + 2 * total ≡ 3 * total
    combine =
      solve 1
        (λ x → x :+ (con 2 :* x) := con 3 :* x)
        refl total
  in
  trans
    (cong₂ _+_ zeroHalf oneHalf)
    (trans combine (cong (3 *_) (weightedTotalPowThree m)))

oneLePowTwo : (n : Nat) → 1 ≤ powNat 2 n
oneLePowTwo zero = NatP.≤-refl
oneLePowTwo (suc n) =
  NatP.≤-trans
    (oneLePowTwo n)
    (NatP.m≤m+n (powNat 2 n) (powNat 2 n))

powTwoMonotone :
  {a b : Nat} →
  a ≤ b →
  powNat 2 a ≤ powNat 2 b
powTwoMonotone {zero} {b} z≤n = oneLePowTwo b
powTwoMonotone {suc a} {suc b} (s≤s a≤b) =
  NatP.*-monoʳ-≤ 2 (powTwoMonotone a≤b)

atLeastIndicator :
  {m : Nat} →
  Nat →
  Binary.BinaryWord m → Nat
atLeastIndicator k word with k ≤ᵇ ones word
... | true = 1
... | false = 0

atLeastCount : Nat → Nat → Nat
atLeastCount m k = wordFold (atLeastIndicator {m} k)

indicatorWeightBound :
  {m k : Nat} →
  (word : Binary.BinaryWord m) →
  powNat 2 k * atLeastIndicator k word ≤ wordWeight word
indicatorWeightBound {k = k} word with k ≤ᵇ ones word in decision
... | false = z≤n
... | true =
  let
    k≤ones : k ≤ ones word
    k≤ones = NatP.≤ᵇ⇒≤ k (ones word) (subst T (sym decision) tt)

    raw : powNat 2 k ≤ wordWeight word
    raw = powTwoMonotone k≤ones
  in
  subst
    (λ left → left ≤ wordWeight word)
    (sym (NatP.*-identityʳ (powNat 2 k)))
    raw

integerChernoff :
  (m k : Nat) →
  powNat 2 k * atLeastCount m k ≤ powNat 3 m
integerChernoff m k =
  let
    scaledCount :
      powNat 2 k * atLeastCount m k
      ≡ wordFold (λ word → powNat 2 k * atLeastIndicator k word)
    scaledCount = scaleFold (powNat 2 k) (atLeastIndicator {m} k)

    pointwiseBound :
      wordFold (λ word → powNat 2 k * atLeastIndicator k word)
      ≤ weightedTotal m
    pointwiseBound =
      foldMono
        (λ word → powNat 2 k * atLeastIndicator k word)
        wordWeight
        indicatorWeightBound

    toPower : weightedTotal m ≤ powNat 3 m
    toPower = NatP.≤-reflexive (weightedTotalPowThree m)
  in
  subst
    (λ left → left ≤ powNat 3 m)
    (sym scaledCount)
    (NatP.≤-trans pointwiseBound toPower)

record IntegerChernoffBoundary : Set where
  constructor integerChernoffBoundary
  field
    exactWeightedTotalOwned : Nat
    exactTailCountOwned : Nat
    integerChernoffOwned : Nat
    measureTheoryRequired : Nat
    independenceHypothesisRequired : Nat

canonicalIntegerChernoffBoundary : IntegerChernoffBoundary
canonicalIntegerChernoffBoundary = integerChernoffBoundary 1 1 1 0 0
