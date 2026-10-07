module DASHI.NumberTheory.Collatz.SyracuseAffineCorrectionBoundExact where

------------------------------------------------------------------------
-- UNIFORM AFFINE-CORRECTION BOUND AND PARITY-COUNT DESCENT
--
-- For every parity word w of length m:
--
--   A(w) < 3^m.
--
-- Hence, for the literal Syracuse orbit, the two elementary conditions
--
--   3^m <= x
--   2 * 3^(ones w) <= 2^m
--
-- imply strict descent after m shortcut steps.  This is a purely integer
-- consumer of the exact affine iterate theorem: no logarithm, Markov chain,
-- or asymptotic approximation is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.NumberTheory.Collatz.SyracuseAffineDescentMarginExact as Descent

powThreePositive :
  (m : Nat) →
  0 < Affine.powNat 3 m
powThreePositive zero = s≤s z≤n
powThreePositive (suc m) =
  NatP.*-mono-<
    (s≤s z≤n)
    (powThreePositive m)

powThreeLeThreeTimes :
  (value : Nat) →
  value ≤ 3 * value
powThreeLeThreeTimes value =
  subst
    (value ≤_)
    (solve 1
      (λ x → x :+ (x :+ x) := con 3 :* x)
      refl value)
    (NatP.m≤m+n value (value + value))

parityPowerBound :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Affine.powNat 3 (Affine.parityCount word)
  ≤ Affine.powNat 3 m
parityPowerBound Binary.end = NatP.≤-refl
parityPowerBound (Binary.bit0 tail) =
  NatP.≤-trans
    (parityPowerBound tail)
    (powThreeLeThreeTimes (Affine.powNat 3 _))
parityPowerBound (Binary.bit1 tail) =
  NatP.*-monoʳ-≤ 3 (parityPowerBound tail)

affineAdditiveTermBound :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Affine.affineAdditiveTerm word < Affine.powNat 3 m
affineAdditiveTermBound Binary.end = s≤s z≤n
affineAdditiveTermBound (Binary.bit0 tail) =
  let
    a = Affine.affineAdditiveTerm tail
    p = Affine.powNat 3 _

    doubledIH : 2 * a < 2 * p
    doubledIH = NatP.*-monoʳ-< 2 (affineAdditiveTermBound tail)

    twoPBelowThreeP : 2 * p < 3 * p
    twoPBelowThreeP =
      subst
        (2 * p <_)
        (solve 1
          (λ x → (x :+ x) :+ x := con 3 :* x)
          refl p)
        (NatP.m<m+n (2 * p) (powThreePositive _))
  in
  NatP.<-trans doubledIH twoPBelowThreeP
affineAdditiveTermBound (Binary.bit1 tail) =
  let
    sPower = Affine.powNat 3 (Affine.parityCount tail)
    a = Affine.affineAdditiveTerm tail
    p = Affine.powNat 3 _

    countLe : sPower ≤ p
    countLe = parityPowerBound tail

    doubledIH : 2 * a < 2 * p
    doubledIH = NatP.*-monoʳ-< 2 (affineAdditiveTermBound tail)

    sumBound : sPower + 2 * a < p + 2 * p
    sumBound = NatP.+-mono-≤-< countLe doubledIH
  in
  subst
    (sPower + 2 * a <_)
    (solve 1
      (λ x → x :+ (con 2 :* x) := con 3 :* x)
      refl p)
    sumBound

oneLePowThree :
  (m : Nat) →
  1 ≤ Affine.powNat 3 m
oneLePowThree m = powThreePositive m

startBelowOddScale :
  (oddCount : Nat) →
  (x : Nat) →
  x ≤ Affine.powNat 3 oddCount * x
startBelowOddScale oddCount x =
  subst
    (x ≤_)
    (NatP.*-identityˡ x)
    (NatP.*-monoˡ-≤ x (oneLePowThree oddCount))

coarseParityMarginImpliesScalarMargin :
  (m : Nat) →
  (x : Syracuse.PositiveNat) →
  Affine.powNat 3 m ≤ Syracuse.toNat x →
  2 * Affine.powNat 3
        (Affine.parityCount (Itinerary.parityWord m x))
    ≤ Affine.powNat 2 m →
  Descent.literalAffineNumerator m x
    < Affine.powNat 2 m * Syracuse.toNat x
coarseParityMarginImpliesScalarMargin m x startLarge drift =
  let
    word = Itinerary.parityWord m x
    s = Affine.parityCount word
    p = Affine.powNat 3 s
    a = Affine.affineAdditiveTerm word
    value = Syracuse.toNat x

    correctionBelowStart : a < value
    correctionBelowStart =
      NatP.<-≤-trans (affineAdditiveTermBound word) startLarge

    startBelowScaled : value ≤ p * value
    startBelowScaled = startBelowOddScale s value

    correctionBelowScaled : a < p * value
    correctionBelowScaled =
      NatP.<-≤-trans correctionBelowStart startBelowScaled

    numeratorBelowDouble :
      p * value + a < p * value + p * value
    numeratorBelowDouble =
      NatP.+-mono-≤-< NatP.≤-refl correctionBelowScaled

    doubleNormalize :
      p * value + p * value ≡ (2 * p) * value
    doubleNormalize =
      solve 2
        (λ p x →
          (p :* x) :+ (p :* x)
          :=
          (con 2 :* p) :* x)
        refl p value

    scaledDrift :
      (2 * p) * value ≤ Affine.powNat 2 m * value
    scaledDrift = NatP.*-monoˡ-≤ value drift
  in
  NatP.<-≤-trans
    (subst
      (Descent.literalAffineNumerator m x <_)
      doubleNormalize
      numeratorBelowDouble)
    scaledDrift

coarseParityMarginImpliesDescent :
  (m : Nat) →
  (x : Syracuse.PositiveNat) →
  Affine.powNat 3 m ≤ Syracuse.toNat x →
  2 * Affine.powNat 3
        (Affine.parityCount (Itinerary.parityWord m x))
    ≤ Affine.powNat 2 m →
  Syracuse.toNat (Syracuse.syracuseIterate m x) < Syracuse.toNat x
coarseParityMarginImpliesDescent m x startLarge drift =
  Descent.strictAffineMarginImpliesDescent m x
    (coarseParityMarginImpliesScalarMargin m x startLarge drift)

record AffineCorrectionBoundary : Set where
  constructor affineCorrectionBoundary
  field
    correctionBoundOwned : Nat
    parityPowerBoundOwned : Nat
    integerDescentCriterionOwned : Nat
    logarithmRequired : Nat
    oddCountTailProbabilityAutomaticallyOwned : Nat

canonicalAffineCorrectionBoundary : AffineCorrectionBoundary
canonicalAffineCorrectionBoundary = affineCorrectionBoundary 1 1 1 0 0
