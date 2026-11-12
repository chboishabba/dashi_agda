module DASHI.Physics.YangMills.BalabanLiteralRightNestedHullExtremaExact where

-- Right-bracketed actual rational four-corner hull = eight-corner hull.
-- Uses source Typed.multiplyIntervalSound and exact rational order;
-- nothing is substituted for the original interval multiplication.

open import Data.Rational.Base as ℚ using (ℚ; _≤_; _*_)
import Data.Rational.Properties as ℚP
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanLiteralEightCornerReassociationExact as Eight
import DASHI.Physics.YangMills.BalabanLiteralFourCornerCommutativityExact as Four
import DASHI.Physics.YangMills.BalabanLiteralHullScalarExtremaExact as Hull
import DASHI.Physics.YangMills.BalabanLiteralLeftNestedHullExtremaExact as Left

-- The exact triple corner list in (x * (y * z)) order.
rightLowerIsEightCornerMinimum : ∀ x y z →
  Eval.lower (Typed.multiplyInterval x (Typed.multiplyInterval y z))
  ≤ Eight.rightCorners Eight.min8 x y z
rightLowerIsEightCornerMinimum x y z =
  Eight.min8Greatest
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Left.lowerInside x)
      (Typed.multiplyIntervalSound (Left.lowerInside y) (Left.lowerInside z))))
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Left.lowerInside x)
      (Typed.multiplyIntervalSound (Left.lowerInside y) (Left.upperInside z))))
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Left.lowerInside x)
      (Typed.multiplyIntervalSound (Left.upperInside y) (Left.lowerInside z))))
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Left.lowerInside x)
      (Typed.multiplyIntervalSound (Left.upperInside y) (Left.upperInside z))))
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Left.upperInside x)
      (Typed.multiplyIntervalSound (Left.lowerInside y) (Left.lowerInside z))))
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Left.upperInside x)
      (Typed.multiplyIntervalSound (Left.lowerInside y) (Left.upperInside z))))
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Left.upperInside x)
      (Typed.multiplyIntervalSound (Left.upperInside y) (Left.lowerInside z))))
    (Typed.lowerSound (Typed.multiplyIntervalSound
      (Left.upperInside x)
      (Typed.multiplyIntervalSound (Left.upperInside y) (Left.upperInside z))))

eightCornerMinimumIsRightLower : ∀ x y z →
  Eight.rightCorners Eight.min8 x y z
  ≤ Eval.lower (Typed.multiplyInterval x (Typed.multiplyInterval y z))
eightCornerMinimumIsRightLower x y z =
  Four.min4Greatest
    (Hull.min4LeftTimesLower (Eval.lower x)
      (Left.min8Below1 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.min8Below2 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.min8Below3 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.min8Below4 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
    )
    (Hull.min4LeftTimesLower (Eval.upper x)
      (Left.min8Below5 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.min8Below6 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.min8Below7 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.min8Below8 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
    )
    (Hull.max4LeftTimesLower (Eval.lower x)
      (Left.min8Below1 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.min8Below2 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.min8Below3 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.min8Below4 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
    )
    (Hull.max4LeftTimesLower (Eval.upper x)
      (Left.min8Below5 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.min8Below6 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.min8Below7 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.min8Below8 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
    )

rightUpperIsEightCornerMaximum : ∀ x y z →
  Eval.upper (Typed.multiplyInterval x (Typed.multiplyInterval y z))
  ≤ Eight.rightCorners Eight.max8 x y z
rightUpperIsEightCornerMaximum x y z =
  Four.max4Least
    (Hull.min4LeftTimesUpper (Eval.lower x)
      (Left.max8Above1 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.max8Above2 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.max8Above3 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.max8Above4 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
    )
    (Hull.min4LeftTimesUpper (Eval.upper x)
      (Left.max8Above5 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.max8Above6 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.max8Above7 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.max8Above8 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
    )
    (Hull.max4LeftTimesUpper (Eval.lower x)
      (Left.max8Above1 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.max8Above2 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.max8Above3 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.max8Above4 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
    )
    (Hull.max4LeftTimesUpper (Eval.upper x)
      (Left.max8Above5 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.max8Above6 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.max8Above7 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
      (Left.max8Above8 (Eval.lower x * (Eval.lower y * Eval.lower z)) (Eval.lower x * (Eval.lower y * Eval.upper z)) (Eval.lower x * (Eval.upper y * Eval.lower z)) (Eval.lower x * (Eval.upper y * Eval.upper z)) (Eval.upper x * (Eval.lower y * Eval.lower z)) (Eval.upper x * (Eval.lower y * Eval.upper z)) (Eval.upper x * (Eval.upper y * Eval.lower z)) (Eval.upper x * (Eval.upper y * Eval.upper z)))
    )

eightCornerMaximumIsRightUpper : ∀ x y z →
  Eight.rightCorners Eight.max8 x y z
  ≤ Eval.upper (Typed.multiplyInterval x (Typed.multiplyInterval y z))
eightCornerMaximumIsRightUpper x y z =
  Eight.max8Least
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Left.lowerInside x)
      (Typed.multiplyIntervalSound (Left.lowerInside y) (Left.lowerInside z))))
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Left.lowerInside x)
      (Typed.multiplyIntervalSound (Left.lowerInside y) (Left.upperInside z))))
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Left.lowerInside x)
      (Typed.multiplyIntervalSound (Left.upperInside y) (Left.lowerInside z))))
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Left.lowerInside x)
      (Typed.multiplyIntervalSound (Left.upperInside y) (Left.upperInside z))))
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Left.upperInside x)
      (Typed.multiplyIntervalSound (Left.lowerInside y) (Left.lowerInside z))))
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Left.upperInside x)
      (Typed.multiplyIntervalSound (Left.lowerInside y) (Left.upperInside z))))
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Left.upperInside x)
      (Typed.multiplyIntervalSound (Left.upperInside y) (Left.lowerInside z))))
    (Typed.upperSound (Typed.multiplyIntervalSound
      (Left.upperInside x)
      (Typed.multiplyIntervalSound (Left.upperInside y) (Left.upperInside z))))

rightLowerEight : ∀ x y z →
  Eval.lower (Typed.multiplyInterval x (Typed.multiplyInterval y z))
    ≡ Eight.rightCorners Eight.min8 x y z
rightLowerEight x y z = ℚP.≤-antisym
  (rightLowerIsEightCornerMinimum x y z)
  (eightCornerMinimumIsRightLower x y z)

rightUpperEight : ∀ x y z →
  Eval.upper (Typed.multiplyInterval x (Typed.multiplyInterval y z))
    ≡ Eight.rightCorners Eight.max8 x y z
rightUpperEight x y z = ℚP.≤-antisym
  (rightUpperIsEightCornerMaximum x y z)
  (eightCornerMaximumIsRightUpper x y z)
