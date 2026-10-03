module DASHI.ComputerScience.TekumPositiveAnchorInjectiveExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_; _∸_)
import Data.Fin.Base as Fin using (toℕ; opposite; fromℕ<)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (+_; ∣_∣)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.DivMod as DivMod using (_%_; [m+n]%n≡m%n; m<n⇒m%n≡m)
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
import DASHI.ComputerScience.TekumSourceAnchorCenterExact as SourceCenter
import DASHI.ComputerScience.TekumWidthAdmissibilityExact as Width

------------------------------------------------------------------------
-- POSITIVE SOURCE WORDS: GENERIC CENTERED FACTS
------------------------------------------------------------------------

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
  rankBound :
    suc m + Positional.center n
    ≤ 2 * Positional.center n
  rankBound =
    subst
      (λ k → k ≤ 2 * Positional.center n)
      (positiveNatCode word valueEq)
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
    let center = Positional.center n in
    subst
      (λ upper → (2 * center ∸ Positional.natCode word) ≤ upper)
      (NatP.m+n∸n≡m center center)
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

------------------------------------------------------------------------
-- CORRECT DEFINITION-7 MIDPOINT COORDINATES
------------------------------------------------------------------------

fourCMinusThreeC :
  (c : Nat) → 2 * (2 * c) ∸ 3 * c ≡ c
fourCMinusThreeC c =
  trans
    (cong (_∸ 3 * c)
      (solve 1
        (λ x → con 2 :* (con 2 :* x) := (con 3 :* x) :+ x)
        refl c))
    (NatP.m+n∸m≡n (3 * c) c)

negatedSourceCenterRank :
  ∀ {n} (even : Width.EvenWidth n) →
  toℕ
    (Centered.rank
      (Fixed.negateCentered
        (Centered.encodeCentered (SourceCenter.sourceAnchorCenterWord n))))
  ≡ SourceCenter.sourceCenterMagnitudeAt even
negatedSourceCenterRank {n} even
  rewrite RankNeg.oppositeRankToNatCode (SourceCenter.sourceAnchorCenterWord n)
        | SourceCenter.centerAtEvenWidth even
        | SourceCenter.sourceCenterNatCodeAtEvenWidth even =
  fourCMinusThreeC (SourceCenter.sourceCenterMagnitudeAt even)

wrapRankToNat :
  ∀ {n} (k : Nat) →
  toℕ (Fixed.wrapRank {n} k) ≡ k % Fixed.modulusSize n
wrapRankToNat {n} k =
  trans
    (FinP.toℕ-cast
      (sym (Centered.pow3RightIsSucTwiceCenter n))
      (fromℕ< (DivMod.m%n<n k (Fixed.modulusSize n))))
    (FinP.toℕ-fromℕ< (DivMod.m%n<n k (Fixed.modulusSize n)))

baseBelowModulus :
  ∀ {n m}
  (even : Width.EvenWidth n) →
  suc m ≤ Positional.center n →
  suc m + SourceCenter.sourceCenterMagnitudeAt even
    < Fixed.modulusSize n
baseBelowModulus {n} {m} even magnitudeBound
  rewrite SourceCenter.centerAtEvenWidth even =
  NatP.≤-<-trans baseAtMostThreeC threeCBelowModulus
  where
  c = SourceCenter.sourceCenterMagnitudeAt even

  baseAtMostThreeC : suc m + c ≤ 3 * c
  baseAtMostThreeC =
    subst
      (λ upper → suc m + c ≤ upper)
      (solve 1 (λ x → (con 2 :* x) :+ x := con 3 :* x) refl c)
      (NatP.+-monoʳ-≤ c magnitudeBound)

  threeCBelowFourCPlusOne : 3 * c < suc (4 * c)
  threeCBelowFourCPlusOne =
    NatP.≤-<-trans
      (subst
        (3 * c ≤_)
        (solve 1 (λ x → (con 3 :* x) :+ x := con 4 :* x) refl c)
        (NatP.m≤m+n (3 * c) c))
      (NatP.n<1+n (4 * c))

  threeCBelowModulus : 3 * c < suc (2 * (2 * c))
  threeCBelowModulus =
    subst
      (3 * c <_)
      (cong suc (solve 1 (λ x → con 4 :* x := con 2 :* (con 2 :* x)) refl c))
      threeCBelowFourCPlusOne

positiveWrapExactEven :
  ∀ {n m}
  (even : Width.EvenWidth n) →
  suc m ≤ Positional.center n →
  ((suc m + Positional.center n)
      + SourceCenter.sourceCenterMagnitudeAt even
      + suc (Positional.center n))
    % Fixed.modulusSize n
  ≡ suc m + SourceCenter.sourceCenterMagnitudeAt even
positiveWrapExactEven {n} {m} even magnitudeBound =
  trans
    (cong (_% Fixed.modulusSize n) totalAsBasePlusModulus)
    (trans
      ([m+n]%n≡m%n
        (suc m + SourceCenter.sourceCenterMagnitudeAt even)
        (Fixed.modulusSize n))
      (m<n⇒m%n≡m (baseBelowModulus even magnitudeBound)))
  where
  c = SourceCenter.sourceCenterMagnitudeAt even

  totalAsBasePlusModulus :
    (suc m + Positional.center n) + c + suc (Positional.center n)
    ≡ (suc m + c) + Fixed.modulusSize n
  totalAsBasePlusModulus
    rewrite SourceCenter.centerAtEvenWidth even =
    solve 2
      (λ a x →
        (a :+ (con 2 :* x)) :+ x :+ (con 1 :+ (con 2 :* x))
        := (a :+ x) :+ (con 1 :+ (con 2 :* (con 2 :* x))))
      refl (suc m) c

------------------------------------------------------------------------
-- THE CORRECTED CONCRETE ANCHOR IS INJECTIVE ON THE POSITIVE HALF.
------------------------------------------------------------------------

positiveConcreteAnchorRank :
  ∀ {n m}
  (even : Width.EvenWidth n)
  (word : Vec Trit.Trit n) →
  BT.toInteger (BT.eval word) ≡ + (suc m) →
  toℕ (Rank.rankWord (Fixed.concreteAnchor word))
  ≡ suc m + SourceCenter.sourceCenterMagnitudeAt even
positiveConcreteAnchorRank {n} {m} even word valueEq =
  trans decodedRank stateRank
  where
  anchorState =
    Fixed.subtractCentered
      (Centered.encodeCentered (Fixed.modulusWord word))
      (Centered.encodeCentered (SourceCenter.sourceAnchorCenterWord n))

  decodedRank :
    toℕ (Rank.rankWord (Fixed.concreteAnchor word))
    ≡ toℕ (Centered.rank anchorState)
  decodedRank =
    cong
      (λ c → toℕ (Centered.rank c))
      (Centered.encodeDecodeCentered anchorState)

  stateRank :
    toℕ (Centered.rank anchorState)
    ≡ suc m + SourceCenter.sourceCenterMagnitudeAt even
  stateRank
    rewrite encodeModulusWordPositive word valueEq
          | Rank.rankToNatCode word
          | positiveNatCode word valueEq
          | negatedSourceCenterRank even =
    trans
      (wrapRankToNat
        ((suc m + Positional.center n)
          + SourceCenter.sourceCenterMagnitudeAt even
          + suc (Positional.center n)))
      (positiveWrapExactEven even (positiveMagnitudeBound word valueEq))

positiveAnchorInjective :
  ∀ {n} {left right : Vec Trit.Trit n} {m k} →
  (even : Width.EvenWidth n) →
  BT.toInteger (BT.eval left) ≡ + (suc m) →
  BT.toInteger (BT.eval right) ≡ + (suc k) →
  Fixed.concreteAnchor left ≡ Fixed.concreteAnchor right →
  left ≡ right
positiveAnchorInjective {left = left} {right = right} {m} {k}
    even leftPositive rightPositive anchorEq =
  Positional.toIntegerInjective integerEq
  where
  c = SourceCenter.sourceCenterMagnitudeAt even

  shiftedMagnitudeEq : suc m + c ≡ suc k + c
  shiftedMagnitudeEq =
    trans
      (sym (positiveConcreteAnchorRank even left leftPositive))
      (trans
        (cong (λ w → toℕ (Rank.rankWord w)) anchorEq)
        (positiveConcreteAnchorRank even right rightPositive))

  magnitudeEq : suc m ≡ suc k
  magnitudeEq = NatP.+-cancelʳ-≡ (suc m) (suc k) c shiftedMagnitudeEq

  integerEq :
    BT.toInteger (BT.eval left) ≡ BT.toInteger (BT.eval right)
  integerEq =
    trans leftPositive
      (trans (cong +_ magnitudeEq) (sym rightPositive))
