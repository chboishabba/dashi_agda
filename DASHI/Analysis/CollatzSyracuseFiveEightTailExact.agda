module DASHI.Analysis.CollatzSyracuseFiveEightTailExact where

------------------------------------------------------------------------
-- FIVE-EIGHTHS PARITY TAIL -> LITERAL SYRACUSE DESCENT
--
-- Use the exact integer comparison
--
--   3^5 = 243 < 256 = 2^8.
--
-- At horizon m = 8n+1, every word with at most 5n odd steps satisfies
--
--   2 * 3^(ones w) <= 2^(8n+1),
--
-- hence is a literal descent word for starts x >= 3^(8n+1).
-- Therefore every bad word lies in the upper tail ones(w) >= 5n+1.  Combining
-- that inclusion with BinaryWordIntegerChernoffExact gives the fully discrete
-- concentration inequality
--
--   2^(5n+1) * badWordCount(8n+1) <= 3^(8n+1).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Bool.Base using (T)
open import Data.Empty using (⊥; contradiction)
open import Data.Nat using (_≤_; _<_; _≤ᵇ_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.Core.BinaryWordIntegerChernoffExact as Chernoff
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseParityDescentEventExact as Event

------------------------------------------------------------------------
-- Shared power / one-count carriers.
------------------------------------------------------------------------

powAgreement :
  (base exponent : Nat) →
  Chernoff.powNat base exponent ≡ Affine.powNat base exponent
powAgreement base zero = refl
powAgreement base (suc exponent) =
  cong (base *_) (powAgreement base exponent)

onesAgreement :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Chernoff.ones word ≡ Affine.parityCount word
onesAgreement Binary.end = refl
onesAgreement (Binary.bit0 tail) = onesAgreement tail
onesAgreement (Binary.bit1 tail) = cong suc (onesAgreement tail)

------------------------------------------------------------------------
-- Elementary power algebra.
------------------------------------------------------------------------

powAdd :
  (base left right : Nat) →
  Affine.powNat base (left + right)
  ≡ Affine.powNat base left * Affine.powNat base right
powAdd base zero right = sym (NatP.*-identityˡ (Affine.powNat base right))
powAdd base (suc left) right =
  trans
    (cong (base *_) (powAdd base left right))
    (sym (NatP.*-assoc base (Affine.powNat base left) (Affine.powNat base right)))

oneLePow :
  (base exponent : Nat) →
  1 ≤ base →
  1 ≤ Affine.powNat base exponent
oneLePow base zero basePositive = NatP.≤-refl
oneLePow base (suc exponent) basePositive =
  NatP.*-mono-≤ basePositive (oneLePow base exponent basePositive)

powMonotoneThree :
  {left right : Nat} →
  left ≤ right →
  Affine.powNat 3 left ≤ Affine.powNat 3 right
powMonotoneThree {zero} {right} z≤n =
  oneLePow 3 right (s≤s z≤n)
powMonotoneThree {suc left} {suc right} (s≤s relation) =
  NatP.*-monoʳ-≤ 3 (powMonotoneThree relation)

------------------------------------------------------------------------
-- 2 * 3^(5n) <= 2^(8n+1).
------------------------------------------------------------------------

threeFiveLeTwoEight :
  Affine.powNat 3 5 ≤ Affine.powNat 2 8
threeFiveLeTwoEight = NatP.≤ᵇ⇒≤ 243 256 tt

fiveEightGrowth :
  (n : Nat) →
  2 * Affine.powNat 3 (5 * n)
  ≤ Affine.powNat 2 (8 * n + 1)
fiveEightGrowth zero = NatP.≤-refl
fiveEightGrowth (suc n) =
  let
    oldLeft = 2 * Affine.powNat 3 (5 * n)
    oldRight = Affine.powNat 2 (8 * n + 1)

    expFive : 5 * suc n ≡ 5 * n + 5
    expFive =
      solve 1
        (λ x → con 5 :* (con 1 :+ x) := (con 5 :* x) :+ con 5)
        refl n

    expEight : 8 * suc n + 1 ≡ (8 * n + 1) + 8
    expEight =
      solve 1
        (λ x →
          (con 8 :* (con 1 :+ x)) :+ con 1
          :=
          ((con 8 :* x) :+ con 1) :+ con 8)
        refl n

    leftFactor :
      2 * Affine.powNat 3 (5 * suc n)
      ≡ Affine.powNat 3 5 * oldLeft
    leftFactor =
      trans
        (cong (λ exponent → 2 * Affine.powNat 3 exponent) expFive)
        (trans
          (cong (2 *_) (powAdd 3 (5 * n) 5))
          (solve 2
            (λ a b → con 2 :* (a :* b) := b :* (con 2 :* a))
            refl
            (Affine.powNat 3 (5 * n))
            (Affine.powNat 3 5)))

    rightFactor :
      Affine.powNat 2 (8 * suc n + 1)
      ≡ Affine.powNat 2 8 * oldRight
    rightFactor =
      trans
        (cong (Affine.powNat 2) expEight)
        (trans
          (powAdd 2 (8 * n + 1) 8)
          (NatP.*-comm
            (Affine.powNat 2 (8 * n + 1))
            (Affine.powNat 2 8)))

    multiplied :
      Affine.powNat 3 5 * oldLeft
      ≤ Affine.powNat 2 8 * oldRight
    multiplied = NatP.*-mono-≤ threeFiveLeTwoEight (fiveEightGrowth n)
  in
  subst
    (λ left → left ≤ Affine.powNat 2 (8 * suc n + 1))
    (sym leftFactor)
    (subst
      (Affine.powNat 3 5 * oldLeft ≤_)
      (sym rightFactor)
      multiplied)

fiveEightGood :
  (n : Nat) →
  {s : Nat} →
  s ≤ 5 * n →
  2 * Affine.powNat 3 s ≤ Affine.powNat 2 (8 * n + 1)
fiveEightGood n s≤5n =
  NatP.≤-trans
    (NatP.*-monoʳ-≤ 2 (powMonotoneThree s≤5n))
    (fiveEightGrowth n)

------------------------------------------------------------------------
-- Bad-word subset of the >=5n+1 tail.
------------------------------------------------------------------------

badWordForcesTail :
  (n : Nat) →
  (word : Binary.BinaryWord (8 * n + 1)) →
  Event.parityDriftGoodᵇ word ≡ false →
  suc (5 * n) ≤ Affine.parityCount word
badWordForcesTail n word bad =
  let
    notSmall : ¬ (Affine.parityCount word ≤ 5 * n)
    notSmall small =
      let
        good : Event.parityDriftGood word
        good = fiveEightGood n small

        reflected : T (Event.parityDriftGoodᵇ word)
        reflected = NatP.≤⇒≤ᵇ good
      in
      contradiction reflected (subst T bad)
  in
  NatP.≰⇒> notSmall

badIndicatorLeTailIndicator :
  (n : Nat) →
  (word : Binary.BinaryOutcomeEnumerationExact.BinaryWord (8 * n + 1)) →
  Event.badIndicator word
  ≤ Chernoff.atLeastIndicator (5 * n + 1) word
badIndicatorLeTailIndicator n word
  with Event.parityDriftGoodᵇ word in goodDecision
... | true = z≤n
... | false
  with (5 * n + 1) ≤ᵇ Chernoff.ones word in tailDecision
...   | true = NatP.≤-refl
...   | false =
  let
    thresholdAffine : suc (5 * n) ≤ Affine.parityCount word
    thresholdAffine = badWordForcesTail n word goodDecision

    thresholdCore : 5 * n + 1 ≤ Chernoff.ones word
    thresholdCore =
      subst
        ((5 * n + 1) ≤_)
        (sym (onesAgreement word))
        thresholdAffine

    reflected : T ((5 * n + 1) ≤ᵇ Chernoff.ones word)
    reflected = NatP.≤⇒≤ᵇ thresholdCore
  in
  contradiction reflected (subst T tailDecision)

badCountLeTailCount :
  (n : Nat) →
  Event.badWordCount (8 * n + 1)
  ≤ Chernoff.atLeastCount (8 * n + 1) (5 * n + 1)
badCountLeTailCount n =
  Chernoff.foldMono
    Event.badIndicator
    (Chernoff.atLeastIndicator (5 * n + 1))
    (badIndicatorLeTailIndicator n)

------------------------------------------------------------------------
-- Integer concentration theorem for the actual bad descent words.
------------------------------------------------------------------------

fiveEightBadWordBound :
  (n : Nat) →
  Chernoff.powNat 2 (5 * n + 1)
    * Event.badWordCount (8 * n + 1)
  ≤ Chernoff.powNat 3 (8 * n + 1)
fiveEightBadWordBound n =
  NatP.≤-trans
    (NatP.*-monoʳ-≤
      (Chernoff.powNat 2 (5 * n + 1))
      (badCountLeTailCount n))
    (Chernoff.integerChernoff (8 * n + 1) (5 * n + 1))

record FiveEightTailBoundary : Set where
  constructor fiveEightTailBoundary
  field
    fiveVsEightPowerComparisonOwned : Nat
    badSubsetTailOwned : Nat
    integerExponentialTailOwned : Nat
    spectralMixingRequired : Nat
    realHoeffdingRequired : Nat
    universalStoppingOwned : Nat

canonicalFiveEightTailBoundary : FiveEightTailBoundary
canonicalFiveEightTailBoundary = fiveEightTailBoundary 1 1 1 0 0 0
