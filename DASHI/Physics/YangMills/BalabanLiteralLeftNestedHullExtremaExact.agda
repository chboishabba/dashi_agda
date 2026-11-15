module DASHI.Physics.YangMills.BalabanLiteralLeftNestedHullExtremaExact where

-- The original four-corner interval product, not a substitute.
-- This module proves both actual left-bracketed extrema coincide with
-- extrema of its eight original rational triple-corner products.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; _*_)
import Data.Rational.Properties as ℚP
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanLiteralEightCornerReassociationExact as Eight
import DASHI.Physics.YangMills.BalabanLiteralFourCornerCommutativityExact as Four
import DASHI.Physics.YangMills.BalabanLiteralHullScalarExtremaExact as Hull

lowerInside : ∀ x → Typed.LiesIn (Eval.lower x) x
lowerInside x = Typed.liesIn ℚP.≤-refl (Eval.ordered x)

upperInside : ∀ x → Typed.LiesIn (Eval.upper x) x
upperInside x = Typed.liesIn (Eval.ordered x) ℚP.≤-refl

min8Below1 : ∀ a b c d e f g h →
  Eight.min8 a b c d e f g h ≤ a
min8Below1 a b c d e f g h =
  ℚP.≤-trans
    (Typed.min2BelowLeft (Typed.min4 a b c d) (Typed.min4 e f g h))
    (Typed.min4BelowFirst a b c d)

max8Above1 : ∀ a b c d e f g h →
  a ≤ Eight.max8 a b c d e f g h
max8Above1 a b c d e f g h =
  ℚP.≤-trans
    (Typed.firstBelowMax4 a b c d)
    (Typed.leftBelowMax2 (Typed.max4 a b c d) (Typed.max4 e f g h))

min8Below2 : ∀ a b c d e f g h →
  Eight.min8 a b c d e f g h ≤ b
min8Below2 a b c d e f g h =
  ℚP.≤-trans
    (Typed.min2BelowLeft (Typed.min4 a b c d) (Typed.min4 e f g h))
    (Typed.min4BelowSecond a b c d)

max8Above2 : ∀ a b c d e f g h →
  b ≤ Eight.max8 a b c d e f g h
max8Above2 a b c d e f g h =
  ℚP.≤-trans
    (Typed.secondBelowMax4 a b c d)
    (Typed.leftBelowMax2 (Typed.max4 a b c d) (Typed.max4 e f g h))

min8Below3 : ∀ a b c d e f g h →
  Eight.min8 a b c d e f g h ≤ c
min8Below3 a b c d e f g h =
  ℚP.≤-trans
    (Typed.min2BelowLeft (Typed.min4 a b c d) (Typed.min4 e f g h))
    (Typed.min4BelowThird a b c d)

max8Above3 : ∀ a b c d e f g h →
  c ≤ Eight.max8 a b c d e f g h
max8Above3 a b c d e f g h =
  ℚP.≤-trans
    (Typed.thirdBelowMax4 a b c d)
    (Typed.leftBelowMax2 (Typed.max4 a b c d) (Typed.max4 e f g h))

min8Below4 : ∀ a b c d e f g h →
  Eight.min8 a b c d e f g h ≤ d
min8Below4 a b c d e f g h =
  ℚP.≤-trans
    (Typed.min2BelowLeft (Typed.min4 a b c d) (Typed.min4 e f g h))
    (Typed.min4BelowFourth a b c d)

max8Above4 : ∀ a b c d e f g h →
  d ≤ Eight.max8 a b c d e f g h
max8Above4 a b c d e f g h =
  ℚP.≤-trans
    (Typed.fourthBelowMax4 a b c d)
    (Typed.leftBelowMax2 (Typed.max4 a b c d) (Typed.max4 e f g h))

min8Below5 : ∀ a b c d e f g h →
  Eight.min8 a b c d e f g h ≤ e
min8Below5 a b c d e f g h =
  ℚP.≤-trans
    (Typed.min2BelowRight (Typed.min4 a b c d) (Typed.min4 e f g h))
    (Typed.min4BelowFirst e f g h)

max8Above5 : ∀ a b c d e f g h →
  e ≤ Eight.max8 a b c d e f g h
max8Above5 a b c d e f g h =
  ℚP.≤-trans
    (Typed.firstBelowMax4 e f g h)
    (Typed.rightBelowMax2 (Typed.max4 a b c d) (Typed.max4 e f g h))

min8Below6 : ∀ a b c d e f g h →
  Eight.min8 a b c d e f g h ≤ f
min8Below6 a b c d e f g h =
  ℚP.≤-trans
    (Typed.min2BelowRight (Typed.min4 a b c d) (Typed.min4 e f g h))
    (Typed.min4BelowSecond e f g h)

max8Above6 : ∀ a b c d e f g h →
  f ≤ Eight.max8 a b c d e f g h
max8Above6 a b c d e f g h =
  ℚP.≤-trans
    (Typed.secondBelowMax4 e f g h)
    (Typed.rightBelowMax2 (Typed.max4 a b c d) (Typed.max4 e f g h))

min8Below7 : ∀ a b c d e f g h →
  Eight.min8 a b c d e f g h ≤ g
min8Below7 a b c d e f g h =
  ℚP.≤-trans
    (Typed.min2BelowRight (Typed.min4 a b c d) (Typed.min4 e f g h))
    (Typed.min4BelowThird e f g h)

max8Above7 : ∀ a b c d e f g h →
  g ≤ Eight.max8 a b c d e f g h
max8Above7 a b c d e f g h =
  ℚP.≤-trans
    (Typed.thirdBelowMax4 e f g h)
    (Typed.rightBelowMax2 (Typed.max4 a b c d) (Typed.max4 e f g h))

min8Below8 : ∀ a b c d e f g h →
  Eight.min8 a b c d e f g h ≤ h
min8Below8 a b c d e f g h =
  ℚP.≤-trans
    (Typed.min2BelowRight (Typed.min4 a b c d) (Typed.min4 e f g h))
    (Typed.min4BelowFourth e f g h)

max8Above8 : ∀ a b c d e f g h →
  h ≤ Eight.max8 a b c d e f g h
max8Above8 a b c d e f g h =
  ℚP.≤-trans
    (Typed.fourthBelowMax4 e f g h)
    (Typed.rightBelowMax2 (Typed.max4 a b c d) (Typed.max4 e f g h))

-- The eight corner order is LL/lowerZ, LL/upperZ, LU/lowerZ,
-- LU/upperZ, UL/lowerZ, UL/upperZ, UU/lowerZ, UU/upperZ.

leftLowerIsEightCornerMinimum : ∀ x y z →
  Eval.lower (Typed.multiplyInterval (Typed.multiplyInterval x y) z)
    ≤ Eight.leftCorners Eight.min8 x y z
leftLowerIsEightCornerMinimum x y z =
  Eight.min8Greatest
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (lowerInside x) (lowerInside y))
      (lowerInside z)))
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (lowerInside x) (lowerInside y))
      (upperInside z)))
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (lowerInside x) (upperInside y))
      (lowerInside z)))
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (lowerInside x) (upperInside y))
      (upperInside z)))
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (upperInside x) (lowerInside y))
      (lowerInside z)))
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (upperInside x) (lowerInside y))
      (upperInside z)))
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (upperInside x) (upperInside y))
      (lowerInside z)))
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (upperInside x) (upperInside y))
      (upperInside z)))

eightCornerMinimumIsLeftLower : ∀ x y z →
  Eight.leftCorners Eight.min8 x y z
    ≤ Eval.lower (Typed.multiplyInterval (Typed.multiplyInterval x y) z)
eightCornerMinimumIsLeftLower x y z =
  Four.min4Greatest
    (Hull.min4TimesLower (Eval.lower z)
      (min8Below1 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (min8Below3 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (min8Below5 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (min8Below7 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
    )
    (Hull.min4TimesLower (Eval.upper z)
      (min8Below2 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (min8Below4 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (min8Below6 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (min8Below8 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
    )
    (Hull.max4TimesLower (Eval.lower z)
      (min8Below1 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (min8Below3 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (min8Below5 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (min8Below7 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
    )
    (Hull.max4TimesLower (Eval.upper z)
      (min8Below2 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (min8Below4 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (min8Below6 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (min8Below8 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
    )

leftUpperIsEightCornerMaximum : ∀ x y z →
  Eval.upper (Typed.multiplyInterval (Typed.multiplyInterval x y) z)
    ≤ Eight.leftCorners Eight.max8 x y z
leftUpperIsEightCornerMaximum x y z =
  Four.max4Least
    (Hull.min4TimesUpper (Eval.lower z)
      (max8Above1 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (max8Above3 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (max8Above5 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (max8Above7 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
    )
    (Hull.min4TimesUpper (Eval.upper z)
      (max8Above2 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (max8Above4 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (max8Above6 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (max8Above8 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
    )
    (Hull.max4TimesUpper (Eval.lower z)
      (max8Above1 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (max8Above3 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (max8Above5 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (max8Above7 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
    )
    (Hull.max4TimesUpper (Eval.upper z)
      (max8Above2 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (max8Above4 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (max8Above6 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
      (max8Above8 ((Eval.lower x * Eval.lower y) * Eval.lower z) ((Eval.lower x * Eval.lower y) * Eval.upper z) ((Eval.lower x * Eval.upper y) * Eval.lower z) ((Eval.lower x * Eval.upper y) * Eval.upper z) ((Eval.upper x * Eval.lower y) * Eval.lower z) ((Eval.upper x * Eval.lower y) * Eval.upper z) ((Eval.upper x * Eval.upper y) * Eval.lower z) ((Eval.upper x * Eval.upper y) * Eval.upper z))
    )

eightCornerMaximumIsLeftUpper : ∀ x y z →
  Eight.leftCorners Eight.max8 x y z
    ≤ Eval.upper (Typed.multiplyInterval (Typed.multiplyInterval x y) z)
eightCornerMaximumIsLeftUpper x y z =
  Eight.max8Least
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (lowerInside x) (lowerInside y))
      (lowerInside z)))
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (lowerInside x) (lowerInside y))
      (upperInside z)))
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (lowerInside x) (upperInside y))
      (lowerInside z)))
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (lowerInside x) (upperInside y))
      (upperInside z)))
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (upperInside x) (lowerInside y))
      (lowerInside z)))
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (upperInside x) (lowerInside y))
      (upperInside z)))
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (upperInside x) (upperInside y))
      (lowerInside z)))
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Typed.multiplyIntervalSound (upperInside x) (upperInside y))
      (upperInside z)))

leftLowerEight : ∀ x y z →
  Eval.lower (Typed.multiplyInterval (Typed.multiplyInterval x y) z)
    ≡ Eight.leftCorners Eight.min8 x y z
leftLowerEight x y z = ℚP.≤-antisym
  (leftLowerIsEightCornerMinimum x y z)
  (eightCornerMinimumIsLeftLower x y z)

leftUpperEight : ∀ x y z →
  Eval.upper (Typed.multiplyInterval (Typed.multiplyInterval x y) z)
    ≡ Eight.leftCorners Eight.max8 x y z
leftUpperEight x y z = ℚP.≤-antisym
  (leftUpperIsEightCornerMaximum x y z)
  (eightCornerMaximumIsLeftUpper x y z)
