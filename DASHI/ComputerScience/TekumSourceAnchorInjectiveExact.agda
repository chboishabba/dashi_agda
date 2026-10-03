module DASHI.ComputerScience.TekumSourceAnchorInjectiveExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base as ℤ using (+_; -[1+_]; -_)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed
import DASHI.ComputerScience.TekumPositiveAnchorInjectiveExact as Positive
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumWidthAdmissibilityExact as Width

------------------------------------------------------------------------
-- EXTERNAL SIGN + CORRECTED CONCRETE ANCHOR RECOVERS THE SOURCE WORD
--
-- The alternating Definition-7 midpoint proof needs the source even-width
-- witness explicitly.  This is not additional mathematics: core Tekum widths
-- are even by definition, and carrying the witness here prevents the old
-- all-positive-midpoint shortcut from silently reappearing.
------------------------------------------------------------------------

invertWordInvolutive :
  ∀ {n} (word : Vec Trit.Trit n) →
  BT.invertWord (BT.invertWord word) ≡ word
invertWordInvolutive [] = refl
invertWordInvolutive (t ∷ ts)
  rewrite Trit.inv-invol t | invertWordInvolutive ts = refl

negateWordInvolutive :
  ∀ {n} (word : Vec Trit.Trit n) →
  Fixed.negateWord (Fixed.negateWord word) ≡ word
negateWordInvolutive word =
  trans
    (Fixed.negateWordIsInvertWord (Fixed.negateWord word))
    (trans
      (cong BT.invertWord (Fixed.negateWordIsInvertWord word))
      (invertWordInvolutive word))

negativeNegatesPositive :
  ∀ {n m}
  (word : Vec Trit.Trit n) →
  BT.toInteger (BT.eval word) ≡ -[1+ m ] →
  BT.toInteger (BT.eval (Fixed.negateWord word)) ≡ + (suc m)
negativeNegatesPositive word valueEq =
  trans
    (cong
      (λ w → BT.toInteger (BT.eval w))
      (Fixed.negateWordIsInvertWord word))
    (trans
      (BT.toIntegerInvertWord word)
      (cong ℤ.-_ valueEq))

sameSignAnchorDeterminesSourceWord :
  ∀ {n} {left right : Vec Trit.Trit n} →
  (even : Width.EvenWidth n) →
  Source.signOfWord left ≡ Source.signOfWord right →
  Fixed.concreteAnchor left ≡ Fixed.concreteAnchor right →
  left ≡ right
sameSignAnchorDeterminesSourceWord {left = left} {right = right}
    even signEq anchorEq
  with BT.toInteger (BT.eval left) in leftValue
     | BT.toInteger (BT.eval right) in rightValue
... | + 0 | + 0 =
  Positional.toIntegerInjective (trans leftValue (sym rightValue))
... | + 0 | + (suc n) =
  ⊥-elim (zeroPositiveImpossible integerSignEq)
  where
  integerSignEq : Anchor.zeroSign ≡ Anchor.positiveSign
  integerSignEq =
    trans (sym (cong Source.signOfInteger leftValue))
      (trans signEq (cong Source.signOfInteger rightValue))
  zeroPositiveImpossible : Anchor.zeroSign ≡ Anchor.positiveSign → ⊥
  zeroPositiveImpossible ()
... | + 0 | -[1+ n ] =
  ⊥-elim (zeroNegativeImpossible integerSignEq)
  where
  integerSignEq : Anchor.zeroSign ≡ Anchor.negativeSign
  integerSignEq =
    trans (sym (cong Source.signOfInteger leftValue))
      (trans signEq (cong Source.signOfInteger rightValue))
  zeroNegativeImpossible : Anchor.zeroSign ≡ Anchor.negativeSign → ⊥
  zeroNegativeImpossible ()
... | + (suc m) | + 0 =
  ⊥-elim (positiveZeroImpossible integerSignEq)
  where
  integerSignEq : Anchor.positiveSign ≡ Anchor.zeroSign
  integerSignEq =
    trans (sym (cong Source.signOfInteger leftValue))
      (trans signEq (cong Source.signOfInteger rightValue))
  positiveZeroImpossible : Anchor.positiveSign ≡ Anchor.zeroSign → ⊥
  positiveZeroImpossible ()
... | + (suc m) | + (suc n) =
  Positive.positiveAnchorInjective even leftValue rightValue anchorEq
... | + (suc m) | -[1+ n ] =
  ⊥-elim (positiveNegativeImpossible integerSignEq)
  where
  integerSignEq : Anchor.positiveSign ≡ Anchor.negativeSign
  integerSignEq =
    trans (sym (cong Source.signOfInteger leftValue))
      (trans signEq (cong Source.signOfInteger rightValue))
  positiveNegativeImpossible : Anchor.positiveSign ≡ Anchor.negativeSign → ⊥
  positiveNegativeImpossible ()
... | -[1+ m ] | + 0 =
  ⊥-elim (negativeZeroImpossible integerSignEq)
  where
  integerSignEq : Anchor.negativeSign ≡ Anchor.zeroSign
  integerSignEq =
    trans (sym (cong Source.signOfInteger leftValue))
      (trans signEq (cong Source.signOfInteger rightValue))
  negativeZeroImpossible : Anchor.negativeSign ≡ Anchor.zeroSign → ⊥
  negativeZeroImpossible ()
... | -[1+ m ] | + (suc n) =
  ⊥-elim (negativePositiveImpossible integerSignEq)
  where
  integerSignEq : Anchor.negativeSign ≡ Anchor.positiveSign
  integerSignEq =
    trans (sym (cong Source.signOfInteger leftValue))
      (trans signEq (cong Source.signOfInteger rightValue))
  negativePositiveImpossible : Anchor.negativeSign ≡ Anchor.positiveSign → ⊥
  negativePositiveImpossible ()
... | -[1+ m ] | -[1+ n ] =
  trans
    (sym (negateWordInvolutive left))
    (trans
      (cong Fixed.negateWord negatedEq)
      (negateWordInvolutive right))
  where
  negatedAnchorEq :
    Fixed.concreteAnchor (Fixed.negateWord left)
    ≡ Fixed.concreteAnchor (Fixed.negateWord right)
  negatedAnchorEq =
    trans
      (Fixed.concreteAnchorNegationInvariant left)
      (trans anchorEq
        (sym (Fixed.concreteAnchorNegationInvariant right)))

  negatedEq : Fixed.negateWord left ≡ Fixed.negateWord right
  negatedEq =
    Positive.positiveAnchorInjective even
      (negativeNegatesPositive left leftValue)
      (negativeNegatesPositive right rightValue)
      negatedAnchorEq
