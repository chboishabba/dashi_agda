module DASHI.ComputerScience.TekumPositiveAnchorInjectiveExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
import Data.Fin.Base as Fin using (toℕ; opposite; fromℕ<)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (+_; ∣_∣)
open import Data.Nat.Base using (_≤_; _<_; _⊔_; _∸_)
import Data.Nat.DivMod as DivMod using (_%_; [m+kn]%n≡m%n; m<n⇒m%n≡m)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.Algebra.BalancedTernaryRankReconstructionExact as Rank
import DASHI.Algebra.BalancedTernaryRankNegationExact as RankNeg
import DASHI.Algebra.BalancedTernaryCenteredReconstructionExact as Centered
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed

------------------------------------------------------------------------
-- THE CONCRETE HUNHOLD ANCHOR IS INJECTIVE ON THE POSITIVE HALF
------------------------------------------------------------------------

allPositiveNatCode :
  (n : Nat) →
  Positional.natCode (Fixed.allPositiveWord n)
  ≡ 2 * Positional.center n
allPositiveNatCode zero = refl
allPositiveNatCode (suc n)
  rewrite allPositiveNatCode n =
  solve 1
    (λ c → con 2 :+ (con 3 :* (con 2 :* c))
      := con 2 :* (con 1 :+ (con 3 :* c)))
    refl (Positional.center n)

positiveNatCode :
  ∀ {n m}
  (word : Vec Trit.Trit n) →
  BT.toInteger (BT.eval word) ≡ + (suc m) →
  Positional.natCode word ≡ suc m + Positional.center n
positiveNatCode word refl =
  cong ℤ.∣_∣ (Positional.natCodeShift word)

rankCodeUpper :
  ∀ {n} (word : Vec Trit.Trit n) →
  Positional.natCode word ≤ 2 * Positional.center n
rankCodeUpper {n} word =
  subst
    (λ k → k ≤ 2 * Positional.center n)
    (Rank.rankToNatCode word)
    (Centered.rankNatAtMostTwiceCenter (Rank.rankWord word))

twiceCenterAsSum :
  (n : Nat) →
  2 * Positional.center n
  ≡ Positional.center n + Positional.center n
twiceCenterAsSum n =
  solve 1 (λ c → con 2 :* c := c :+ c) refl (Positional.center n)

twiceCenterMinusCenter :
  (n : Nat) →
  (2 * Positional.center n) ∸ Positional.center n
  ≡ Positional.center n
twiceCenterMinusCenter n
  rewrite twiceCenterAsSum n =
  NatP.m+n∸n≡m (Positional.center n) (Positional.center n)

positiveMagnitudeBound :
  ∀ {n m}
  (word : Vec Trit.Trit n) →
  BT.toInteger (BT.eval word) ≡ + (suc m) →
  suc m ≤ Positional.center n
positiveMagnitudeBound {n} {m} word valueEq =
  NatP.+-cancelʳ-≤
    (Positional.center n)
    (suc m)
    (Positional.center n)
    boundWithCommonTail
  where
  codeEq = positiveNatCode word valueEq

  rankBound :
    suc m + Positional.center n
    ≤ 2 * Positional.center n
  rankBound =
    subst
      (λ k → k ≤ 2 * Positional.center n)
      codeEq
      (rankCodeUpper word)

  boundWithCommonTail :
    suc m + Positional.center n
    ≤ Positional.center n + Positional.center n
  boundWithCommonTail =
    subst
      (λ upper → suc m + Positional.center n ≤ upper)
      (twiceCenterAsSum n)
      rankBound

positiveCenterBelowRank :
  ∀ {n m}
  (word : Vec Trit.Trit n) →
  BT.toInteger (BT.eval word) ≡ + (suc m) →
  Positional.center n ≤ Positional.natCode word
positiveCenterBelowRank {n} {m} word valueEq =
  subst
    (Positional.center n ≤_)
    (sym (positiveNatCode word valueEq))
    (NatP.n≤m+n (suc m) (Positional.center n))

positiveOppositeBelowRank :
  ∀ {n m}
  (word : Vec Trit.Trit n) →
  BT.toInteger (BT.eval word) ≡ + (suc m) →
  toℕ (opposite (Rank.rankWord word))
  ≤ toℕ (Rank.rankWord word)
positiveOppositeBelowRank {n} word valueEq =
  subst
    (λ oppositeCode → oppositeCode ≤ toℕ (Rank.rankWord word))
    (sym (RankNeg.oppositeRankToNatCode word))
    (NatP.≤-trans complementBelowCenter centerBelowRank)
  where
  centerBelowRank :
    Positional.center n ≤ toℕ (Rank.rankWord word)
  centerBelowRank =
    subst
      (Positional.center n ≤_)
      (sym (Rank.rankToNatCode word))
      (positiveCenterBelowRank word valueEq)

  complementBelowCenter :
    (2 * Positional.center n ∸ Positional.natCode word)
    ≤ Positional.center n
  complementBelowCenter =
    subst
      (λ upper →
        (2 * Positional.center n ∸ Positional.natCode word) ≤ upper)
      (twiceCenterMinusCenter n)
      (NatP.∸-mono NatP.≤-refl (positiveCenterBelowRank word valueEq))

positiveModulusCentered :
  ∀ {n m}
  (word : Vec Trit.Trit n) →
  BT.toInteger (BT.eval word) ≡ + (suc m) →
  Fixed.modulusCentered (Centered.encodeCentered word)
  ≡ Centered.encodeCentered word
positiveModulusCentered word valueEq =
  cong Centered.centeredInteger
    (FinP.toℕ-injective maxIsOriginal)
  where
  r = Rank.rankWord word

  maxIsOriginal :
    toℕ (Fixed.maxRank r (opposite r)) ≡ toℕ r
  maxIsOriginal =
    trans
      (Fixed.maxRankToNat r (opposite r))
      (NatP.m≥n⇒m⊔n≡m (positiveOppositeBelowRank word valueEq))

encodeModulusWordPositive :
  ∀ {n m}
  (word : Vec Trit.Trit n) →
  BT.toInteger (BT.eval word) ≡ + (suc m) →
  Centered.encodeCentered (Fixed.modulusWord word)
  ≡ Centered.encodeCentered word
encodeModulusWordPositive word valueEq =
  trans
    (Centered.encodeDecodeCentered
      (Fixed.modulusCentered (Centered.encodeCentered word)))
    (positiveModulusCentered word valueEq)

negatedAllPositiveRankZero :
  (n : Nat) →
  toℕ
    (Centered.rank
      (Fixed.negateCentered
        (Centered.encodeCentered (Fixed.allPositiveWord n))))
  ≡ 0
negatedAllPositiveRankZero n =
  trans
    (RankNeg.oppositeRankToNatCode (Fixed.allPositiveWord n))
    (trans
      (cong (2 * Positional.center n ∸_) (allPositiveNatCode n))
      (NatP.n∸n≡0 (2 * Positional.center n)))

wrapRankToNat :
  ∀ {n} (k : Nat) →
  toℕ (Fixed.wrapRank {n} k) ≡ k % Fixed.modulusSize n
wrapRankToNat {n} k =
  trans
    (FinP.toℕ-cast
      (sym (Centered.pow3RightIsSucTwiceCenter n))
      (fromℕ< (DivMod.m%n<n k (Fixed.modulusSize n))))
    (FinP.toℕ-fromℕ< (DivMod.m%n<n k (Fixed.modulusSize n)))

centerBelowModulus :
  (n : Nat) → Positional.center n < Fixed.modulusSize n
centerBelowModulus n =
  NatP.≤-<-trans
    (subst
      (Positional.center n ≤_)
      (sym (twiceCenterAsSum n))
      (NatP.m≤m+n (Positional.center n) (Positional.center n)))
    (NatP.n<1+n (2 * Positional.center n))

positiveWrapExact :
  ∀ {n m} →
  suc m ≤ Positional.center n →
  ((suc m + Positional.center n) + 0 + suc (Positional.center n))
    % Fixed.modulusSize n
  ≡ suc m
positiveWrapExact {n} {m} magnitudeBound =
  trans
    (cong
      (_% Fixed.modulusSize n)
      (solve 2
        (λ a c →
          (a :+ c) :+ con 0 :+ (con 1 :+ c)
          := a :+ (con 1 :+ (con 2 :* c)))
        refl (suc m) (Positional.center n)))
    (trans
      ([m+kn]%n≡m%n (suc m) 1 (Fixed.modulusSize n))
      (m<n⇒m%n≡m magnitudeBelowModulus))
  where
  magnitudeBelowModulus : suc m < Fixed.modulusSize n
  magnitudeBelowModulus =
    NatP.≤-<-trans magnitudeBound (centerBelowModulus n)

positiveConcreteAnchorRank :
  ∀ {n m}
  (word : Vec Trit.Trit n) →
  BT.toInteger (BT.eval word) ≡ + (suc m) →
  toℕ (Rank.rankWord (Fixed.concreteAnchor word)) ≡ suc m
positiveConcreteAnchorRank {n} {m} word valueEq =
  trans decodedRank stateRank
  where
  anchorState =
    Fixed.subtractCentered
      (Centered.encodeCentered (Fixed.modulusWord word))
      (Centered.encodeCentered (Fixed.allPositiveWord n))

  decodedRank :
    toℕ (Rank.rankWord (Fixed.concreteAnchor word))
    ≡ toℕ (Centered.rank anchorState)
  decodedRank =
    cong
      (λ c → toℕ (Centered.rank c))
      (Centered.encodeDecodeCentered anchorState)

  stateRank : toℕ (Centered.rank anchorState) ≡ suc m
  stateRank
    rewrite encodeModulusWordPositive word valueEq
          | Rank.rankToNatCode word
          | positiveNatCode word valueEq
          | negatedAllPositiveRankZero n =
    trans
      (wrapRankToNat
        ((suc m + Positional.center n) + 0 + suc (Positional.center n)))
      (positiveWrapExact (positiveMagnitudeBound word valueEq))

positiveAnchorInjective :
  ∀ {n} {left right : Vec Trit.Trit n} {m k} →
  BT.toInteger (BT.eval left) ≡ + (suc m) →
  BT.toInteger (BT.eval right) ≡ + (suc k) →
  Fixed.concreteAnchor left ≡ Fixed.concreteAnchor right →
  left ≡ right
positiveAnchorInjective {left = left} {right = right} leftPositive rightPositive anchorEq =
  Positional.toIntegerInjective integerEq
  where
  magnitudeEq : suc _ ≡ suc _
  magnitudeEq =
    trans
      (sym (positiveConcreteAnchorRank left leftPositive))
      (trans
        (cong (λ w → toℕ (Rank.rankWord w)) anchorEq)
        (positiveConcreteAnchorRank right rightPositive))

  integerEq :
    BT.toInteger (BT.eval left) ≡ BT.toInteger (BT.eval right)
  integerEq =
    trans leftPositive
      (trans (cong +_ magnitudeEq) (sym rightPositive))
