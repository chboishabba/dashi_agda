module DASHI.Analysis.CollatzSyracuseRationalDriftTailExact where

------------------------------------------------------------------------
-- PARAMETRIC RATIONAL PARITY-DRIFT TAIL
--
-- The five-eighths theorem is only one integer instance of a more general
-- finite argument.  If
--
--   3^a <= 2^b,
--
-- then at horizon m = b*n + 1 every parity word with at most a*n odd steps
-- satisfies the literal affine descent margin
--
--   2 * 3^(ones w) <= 2^m.
--
-- Hence every bad word lies in the tail ones(w) >= a*n+1, and the exact
-- integer Chernoff theorem gives
--
--   2^(a*n+1) * badWordCount(b*n+1) <= 3^(b*n+1).
--
-- No logarithm, probability measure, spectral gap, or asymptotic theorem is
-- used.  Rational approximants to log_3(2) enter only through the explicit
-- integer power comparison 3^a <= 2^b.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Bool.Base using (T)
open import Data.Nat using (_≤_; _≤ᵇ_; z≤n)
import Data.Nat.Properties as NatP
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)

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
  oneLePow 3 right (NatP.s≤s z≤n)
powMonotoneThree {suc left} {suc right} (NatP.s≤s relation) =
  NatP.*-monoʳ-≤ 3 (powMonotoneThree relation)

------------------------------------------------------------------------
-- 3^a <= 2^b  ==>  2 * 3^(a*n) <= 2^(b*n+1).
------------------------------------------------------------------------

rationalGrowth :
  (a b : Nat) →
  Affine.powNat 3 a ≤ Affine.powNat 2 b →
  (n : Nat) →
  2 * Affine.powNat 3 (a * n)
  ≤ Affine.powNat 2 (b * n + 1)
rationalGrowth a b step zero = NatP.≤-refl
rationalGrowth a b step (suc n) =
  let
    oldLeft = 2 * Affine.powNat 3 (a * n)
    oldRight = Affine.powNat 2 (b * n + 1)

    expA : a * suc n ≡ a * n + a
    expA =
      trans
        (NatP.*-suc a n)
        (NatP.+-comm a (a * n))

    expB : b * suc n + 1 ≡ (b * n + 1) + b
    expB =
      trans
        (cong (_+ 1) (NatP.*-suc b n))
        (trans
          (NatP.+-assoc b (b * n) 1)
          (trans
            (cong (b +_) (NatP.+-comm (b * n) 1))
            (sym (NatP.+-assoc (b * n) 1 b))))

    leftFactor :
      2 * Affine.powNat 3 (a * suc n)
      ≡ Affine.powNat 3 a * oldLeft
    leftFactor =
      trans
        (cong (λ exponent → 2 * Affine.powNat 3 exponent) expA)
        (trans
          (cong (2 *_) (powAdd 3 (a * n) a))
          (trans
            (NatP.*-assoc 2 (Affine.powNat 3 (a * n)) (Affine.powNat 3 a))
            (trans
              (cong (_* Affine.powNat 3 a)
                (NatP.*-comm 2 (Affine.powNat 3 (a * n))))
              (trans
                (sym (NatP.*-assoc
                  (Affine.powNat 3 (a * n)) 2 (Affine.powNat 3 a)))
                (trans
                  (cong (Affine.powNat 3 (a * n) *_)
                    (NatP.*-comm 2 (Affine.powNat 3 a)))
                  (NatP.*-assoc
                    (Affine.powNat 3 (a * n))
                    (Affine.powNat 3 a)
                    2))))))

    rightFactor :
      Affine.powNat 2 (b * suc n + 1)
      ≡ Affine.powNat 2 b * oldRight
    rightFactor =
      trans
        (cong (Affine.powNat 2) expB)
        (trans
          (powAdd 2 (b * n + 1) b)
          (NatP.*-comm
            (Affine.powNat 2 (b * n + 1))
            (Affine.powNat 2 b)))

    multiplied :
      Affine.powNat 3 a * oldLeft
      ≤ Affine.powNat 2 b * oldRight
    multiplied = NatP.*-mono-≤ step (rationalGrowth a b step n)
  in
  subst
    (λ left → left ≤ Affine.powNat 2 (b * suc n + 1))
    (sym leftFactor)
    (subst
      (Affine.powNat 3 a * oldLeft ≤_)
      (sym rightFactor)
      multiplied)

rationalGood :
  (a b n : Nat) →
  Affine.powNat 3 a ≤ Affine.powNat 2 b →
  {s : Nat} →
  s ≤ a * n →
  2 * Affine.powNat 3 s ≤ Affine.powNat 2 (b * n + 1)
rationalGood a b n step s≤an =
  NatP.≤-trans
    (NatP.*-monoʳ-≤ 2 (powMonotoneThree s≤an))
    (rationalGrowth a b step n)

------------------------------------------------------------------------
-- Bad-word subset of the >= a*n+1 tail.
------------------------------------------------------------------------

badWordForcesRationalTail :
  (a b n : Nat) →
  (step : Affine.powNat 3 a ≤ Affine.powNat 2 b) →
  (word : Binary.BinaryWord (b * n + 1)) →
  Event.parityDriftGoodᵇ word ≡ false →
  suc (a * n) ≤ Affine.parityCount word
badWordForcesRationalTail a b n step word bad =
  let
    notSmall : ¬ (Affine.parityCount word ≤ a * n)
    notSmall small =
      let
        good : Event.parityDriftGood word
        good = rationalGood a b n step small

        reflected : T (Event.parityDriftGoodᵇ word)
        reflected = NatP.≤⇒≤ᵇ good
      in
      contradiction reflected (subst T bad)
  in
  NatP.≰⇒> notSmall

badIndicatorLeRationalTailIndicator :
  (a b n : Nat) →
  (step : Affine.powNat 3 a ≤ Affine.powNat 2 b) →
  (word : Binary.BinaryWord (b * n + 1)) →
  Event.badIndicator word
  ≤ Chernoff.atLeastIndicator (a * n + 1) word
badIndicatorLeRationalTailIndicator a b n step word
  with Event.parityDriftGoodᵇ word in goodDecision
... | true = z≤n
... | false
  with (a * n + 1) ≤ᵇ Chernoff.ones word in tailDecision
...   | true = NatP.≤-refl
...   | false =
  let
    thresholdAffine : suc (a * n) ≤ Affine.parityCount word
    thresholdAffine = badWordForcesRationalTail a b n step word goodDecision

    thresholdCore : a * n + 1 ≤ Chernoff.ones word
    thresholdCore =
      subst
        ((a * n + 1) ≤_)
        (sym (onesAgreement word))
        thresholdAffine

    reflected : T ((a * n + 1) ≤ᵇ Chernoff.ones word)
    reflected = NatP.≤⇒≤ᵇ thresholdCore
  in
  contradiction reflected (subst T tailDecision)

badCountLeRationalTailCount :
  (a b n : Nat) →
  (step : Affine.powNat 3 a ≤ Affine.powNat 2 b) →
  Event.badWordCount (b * n + 1)
  ≤ Chernoff.atLeastCount (b * n + 1) (a * n + 1)
badCountLeRationalTailCount a b n step =
  Chernoff.foldMono
    Event.badIndicator
    (Chernoff.atLeastIndicator (a * n + 1))
    (badIndicatorLeRationalTailIndicator a b n step)

------------------------------------------------------------------------
-- Parametric integer concentration theorem.
------------------------------------------------------------------------

rationalBadWordBound :
  (a b n : Nat) →
  (step : Affine.powNat 3 a ≤ Affine.powNat 2 b) →
  Chernoff.powNat 2 (a * n + 1)
    * Event.badWordCount (b * n + 1)
  ≤ Chernoff.powNat 3 (b * n + 1)
rationalBadWordBound a b n step =
  NatP.≤-trans
    (NatP.*-monoʳ-≤
      (Chernoff.powNat 2 (a * n + 1))
      (badCountLeRationalTailCount a b n step))
    (Chernoff.integerChernoff (b * n + 1) (a * n + 1))

record RationalDriftTailBoundary : Set where
  constructor rationalDriftTailBoundary
  field
    powerComparisonExplicit : Nat
    rationalThresholdParametric : Nat
    exactIntegerTailOwned : Nat
    logarithmRequired : Nat
    spectralMixingRequired : Nat
    universalStoppingOwned : Nat

canonicalRationalDriftTailBoundary : RationalDriftTailBoundary
canonicalRationalDriftTailBoundary =
  rationalDriftTailBoundary 1 1 1 0 0 0
