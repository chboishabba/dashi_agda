module DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / INTERVAL REFERENCE
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721.
--
-- DASHI CONTRIBUTION
--
-- Replace the opaque `recursiveEvaluationSound : Set` shape of the literal
-- one-loop box evaluator by an inductive, typed interval derivation over its
-- actual DiagramExpression syntax.
--
-- The arithmetic layer below proves exact rational interval soundness for:
--
--   constant, +, -, unary -, multiplication, and division by an interval
--   whose lower endpoint is strictly positive.
--
-- Multiplication uses the exact four-corner hull.  Division uses the
-- sign-aware positive-denominator theorem from
-- BalabanClayT4PositiveDenominatorQuotientEndpointsExact.
--
-- `ExpressionInterval atomBoxes expression result` is not a receipt saying
-- that `result` is sound.  It is a derivation whose constructors FORCE result
-- to be the interval obtained by recursively applying those proved arithmetic
-- operations.  At a division node the only extra datum is the typed rational
-- inequality `0 < lower denominatorInterval`.
--
-- Finally `evaluateDerivation` proves semantic membership by induction.  Its
-- only source-facing leaves are the values of the literal trig/momentum atoms
-- and proofs that those values lie in `atomBoxes`.  Hence all recursive
-- rational arithmetic soundness is now machine algebra rather than an opaque
-- per-box input.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; -_; _*_; _≤_; _<_; NonNegative; NonPositive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

------------------------------------------------------------------------
-- Semantic membership.
------------------------------------------------------------------------

record LiesIn (value : ℚ) (box : Eval.RationalInterval) : Set where
  constructor liesIn
  field
    lowerSound : Eval.lower box ≤ value
    upperSound : value ≤ Eval.upper box
open LiesIn public

constantInterval : ℚ → Eval.RationalInterval
constantInterval value = Eval.interval value value ℚP.≤-refl

addInterval : Eval.RationalInterval → Eval.RationalInterval → Eval.RationalInterval
addInterval left right = Eval.interval
  (Eval.lower left + Eval.lower right)
  (Eval.upper left + Eval.upper right)
  (ℚP.+-mono-≤ (Eval.ordered left) (Eval.ordered right))

negateInterval : Eval.RationalInterval → Eval.RationalInterval
negateInterval value = Eval.interval
  (- Eval.upper value)
  (- Eval.lower value)
  (ℚP.neg-mono-≤ (Eval.ordered value))

subtractInterval : Eval.RationalInterval → Eval.RationalInterval → Eval.RationalInterval
subtractInterval left right = addInterval left (negateInterval right)

addIntervalSound :
  ∀ {leftValue rightValue left right} →
  LiesIn leftValue left → LiesIn rightValue right →
  LiesIn (leftValue + rightValue) (addInterval left right)
addIntervalSound leftIn rightIn = liesIn
  (ℚP.+-mono-≤ (lowerSound leftIn) (lowerSound rightIn))
  (ℚP.+-mono-≤ (upperSound leftIn) (upperSound rightIn))

negateIntervalSound :
  ∀ {value box} → LiesIn value box →
  LiesIn (- value) (negateInterval box)
negateIntervalSound inside = liesIn
  (ℚP.neg-mono-≤ (upperSound inside))
  (ℚP.neg-mono-≤ (lowerSound inside))

subtractIntervalSound :
  ∀ {leftValue rightValue left right} →
  LiesIn leftValue left → LiesIn rightValue right →
  LiesIn (leftValue - rightValue) (subtractInterval left right)
subtractIntervalSound leftIn rightIn =
  addIntervalSound leftIn (negateIntervalSound rightIn)

------------------------------------------------------------------------
-- Four-corner multiplication hull.
------------------------------------------------------------------------

min2 : ℚ → ℚ → ℚ
min2 left right with ℚP.≤-total left right
... | inj₁ _ = left
... | inj₂ _ = right

max2 : ℚ → ℚ → ℚ
max2 left right with ℚP.≤-total left right
... | inj₁ _ = right
... | inj₂ _ = left

min2BelowLeft : ∀ left right → min2 left right ≤ left
min2BelowLeft left right with ℚP.≤-total left right
... | inj₁ _ = ℚP.≤-refl
... | inj₂ rightBelow = rightBelow

min2BelowRight : ∀ left right → min2 left right ≤ right
min2BelowRight left right with ℚP.≤-total left right
... | inj₁ leftBelow = leftBelow
... | inj₂ _ = ℚP.≤-refl

leftBelowMax2 : ∀ left right → left ≤ max2 left right
leftBelowMax2 left right with ℚP.≤-total left right
... | inj₁ leftBelow = leftBelow
... | inj₂ _ = ℚP.≤-refl

rightBelowMax2 : ∀ left right → right ≤ max2 left right
rightBelowMax2 left right with ℚP.≤-total left right
... | inj₁ _ = ℚP.≤-refl
... | inj₂ rightBelow = rightBelow

min4 : ℚ → ℚ → ℚ → ℚ → ℚ
min4 first second third fourth =
  min2 (min2 first second) (min2 third fourth)

max4 : ℚ → ℚ → ℚ → ℚ → ℚ
max4 first second third fourth =
  max2 (max2 first second) (max2 third fourth)

min4BelowFirst : ∀ a b c d → min4 a b c d ≤ a
min4BelowFirst a b c d =
  ℚP.≤-trans
    (min2BelowLeft (min2 a b) (min2 c d))
    (min2BelowLeft a b)

min4BelowSecond : ∀ a b c d → min4 a b c d ≤ b
min4BelowSecond a b c d =
  ℚP.≤-trans
    (min2BelowLeft (min2 a b) (min2 c d))
    (min2BelowRight a b)

min4BelowThird : ∀ a b c d → min4 a b c d ≤ c
min4BelowThird a b c d =
  ℚP.≤-trans
    (min2BelowRight (min2 a b) (min2 c d))
    (min2BelowLeft c d)

min4BelowFourth : ∀ a b c d → min4 a b c d ≤ d
min4BelowFourth a b c d =
  ℚP.≤-trans
    (min2BelowRight (min2 a b) (min2 c d))
    (min2BelowRight c d)

firstBelowMax4 : ∀ a b c d → a ≤ max4 a b c d
firstBelowMax4 a b c d =
  ℚP.≤-trans
    (leftBelowMax2 a b)
    (leftBelowMax2 (max2 a b) (max2 c d))

secondBelowMax4 : ∀ a b c d → b ≤ max4 a b c d
secondBelowMax4 a b c d =
  ℚP.≤-trans
    (rightBelowMax2 a b)
    (leftBelowMax2 (max2 a b) (max2 c d))

thirdBelowMax4 : ∀ a b c d → c ≤ max4 a b c d
thirdBelowMax4 a b c d =
  ℚP.≤-trans
    (leftBelowMax2 c d)
    (rightBelowMax2 (max2 a b) (max2 c d))

fourthBelowMax4 : ∀ a b c d → d ≤ max4 a b c d
fourthBelowMax4 a b c d =
  ℚP.≤-trans
    (rightBelowMax2 c d)
    (rightBelowMax2 (max2 a b) (max2 c d))

record ProductCorners (left right : Eval.RationalInterval) : Set where
  constructor corners
  field
    lowerLower lowerUpper upperLower upperUpper : ℚ
open ProductCorners public

productCorners : Eval.RationalInterval → Eval.RationalInterval → ProductCorners _ _
productCorners left right = corners
  (Eval.lower left * Eval.lower right)
  (Eval.lower left * Eval.upper right)
  (Eval.upper left * Eval.lower right)
  (Eval.upper left * Eval.upper right)

multiplyInterval : Eval.RationalInterval → Eval.RationalInterval → Eval.RationalInterval
multiplyInterval left right =
  let c = productCorners left right in
  Eval.interval
    (min4
      (lowerLower c) (lowerUpper c) (upperLower c) (upperUpper c))
    (max4
      (lowerLower c) (lowerUpper c) (upperLower c) (upperUpper c))
    (ℚP.≤-trans
      (min4BelowFirst
        (lowerLower c) (lowerUpper c) (upperLower c) (upperUpper c))
      (firstBelowMax4
        (lowerLower c) (lowerUpper c) (upperLower c) (upperUpper c)))

data IntervalSign (lower upper : ℚ) : Set where
  nonnegative : 0ℚ ≤ lower → IntervalSign lower upper
  nonpositive : upper ≤ 0ℚ → IntervalSign lower upper
  straddlesZero : lower ≤ 0ℚ → 0ℚ ≤ upper → IntervalSign lower upper

intervalSign : (box : Eval.RationalInterval) →
  IntervalSign (Eval.lower box) (Eval.upper box)
intervalSign box with ℚP.≤-total 0ℚ (Eval.lower box)
... | inj₁ lowerNN = nonnegative lowerNN
... | inj₂ lowerNP with ℚP.≤-total (Eval.upper box) 0ℚ
...   | inj₁ upperNP = nonpositive upperNP
...   | inj₂ upperNN = straddlesZero lowerNP upperNN

mulRightNN : ∀ scalar {left right} →
  0ℚ ≤ scalar → left ≤ right → left * scalar ≤ right * scalar
mulRightNN scalar scalarNN inequality =
  let instance scalarNonnegative : NonNegative scalar
      scalarNonnegative = ℚ.nonNegative scalarNN
  in ℚP.*-monoʳ-≤-nonNeg scalar inequality

mulLeftNN : ∀ scalar {left right} →
  0ℚ ≤ scalar → left ≤ right → scalar * left ≤ scalar * right
mulLeftNN scalar scalarNN inequality =
  let instance scalarNonnegative : NonNegative scalar
      scalarNonnegative = ℚ.nonNegative scalarNN
  in ℚP.*-monoˡ-≤-nonNeg scalar inequality

mulRightNP : ∀ scalar {left right} →
  scalar ≤ 0ℚ → left ≤ right → right * scalar ≤ left * scalar
mulRightNP scalar scalarNP inequality =
  let instance scalarNonpositive : NonPositive scalar
      scalarNonpositive = ℚ.nonPositive scalarNP
  in ℚP.*-monoʳ-≤-nonPos scalar inequality

mulLeftNP : ∀ scalar {left right} →
  scalar ≤ 0ℚ → left ≤ right → scalar * right ≤ scalar * left
mulLeftNP scalar scalarNP inequality =
  let instance scalarNonpositive : NonPositive scalar
      scalarNonpositive = ℚ.nonPositive scalarNP
  in ℚP.*-monoˡ-≤-nonPos scalar inequality

productNN : ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
productNN left right leftNN rightNN =
  subst
    (λ lower → lower ≤ left * right)
    (ℚRing.solve-∀ right)
    (mulRightNN right rightNN leftNN)

productNP : ∀ left right →
  left ≤ 0ℚ → 0ℚ ≤ right → left * right ≤ 0ℚ
productNP left right leftNP rightNN =
  subst
    (λ upper → left * right ≤ upper)
    (ℚRing.solve-∀ right)
    (mulRightNN right rightNN leftNP)

productPN : ∀ left right →
  0ℚ ≤ left → right ≤ 0ℚ → left * right ≤ 0ℚ
productPN left right leftNN rightNP =
  subst
    (λ upper → left * right ≤ upper)
    (ℚRing.solve-∀ left)
    (mulLeftNN left leftNN rightNP)

productPP : ∀ left right →
  left ≤ 0ℚ → right ≤ 0ℚ → 0ℚ ≤ left * right
productPP left right leftNP rightNP =
  subst
    (λ lower → lower ≤ left * right)
    (ℚRing.solve-∀ right)
    (mulRightNP right rightNP leftNP)

multiplyIntervalSound :
  ∀ {leftValue rightValue left right} →
  LiesIn leftValue left → LiesIn rightValue right →
  LiesIn (leftValue * rightValue) (multiplyInterval left right)
multiplyIntervalSound {leftValue = x} {rightValue = y} {left} {right}
    xIn yIn
  with intervalSign left | intervalSign right
... | nonnegative lNN | nonnegative rNN =
  let
    ll = Eval.lower left * Eval.lower right
    lu = Eval.lower left * Eval.upper right
    ul = Eval.upper left * Eval.lower right
    uu = Eval.upper left * Eval.upper right
    xNN = ℚP.≤-trans lNN (lowerSound xIn)
    yNN = ℚP.≤-trans rNN (lowerSound yIn)
    uLNN = ℚP.≤-trans lNN (Eval.ordered left)
    uRNN = ℚP.≤-trans rNN (Eval.ordered right)
    lowerCorner : ll ≤ x * y
    lowerCorner = ℚP.≤-trans
      (mulRightNN (Eval.lower right) rNN (lowerSound xIn))
      (mulLeftNN x xNN (lowerSound yIn))
    upperCorner : x * y ≤ uu
    upperCorner = ℚP.≤-trans
      (mulRightNN y yNN (upperSound xIn))
      (mulLeftNN (Eval.upper left) uLNN (upperSound yIn))
  in liesIn
    (ℚP.≤-trans (min4BelowFirst ll lu ul uu) lowerCorner)
    (ℚP.≤-trans upperCorner (fourthBelowMax4 ll lu ul uu))
... | nonnegative lNN | nonpositive rNP =
  let
    ll = Eval.lower left * Eval.lower right
    lu = Eval.lower left * Eval.upper right
    ul = Eval.upper left * Eval.lower right
    uu = Eval.upper left * Eval.upper right
    xNN = ℚP.≤-trans lNN (lowerSound xIn)
    yNP = ℚP.≤-trans (upperSound yIn) rNP
    lowerRNP = ℚP.≤-trans (Eval.ordered right) rNP
    upperLNN = ℚP.≤-trans lNN (Eval.ordered left)
    lowerCorner : ul ≤ x * y
    lowerCorner = ℚP.≤-trans
      (mulRightNP (Eval.lower right) lowerRNP (upperSound xIn))
      (mulLeftNN x xNN (lowerSound yIn))
    upperCorner : x * y ≤ lu
    upperCorner = ℚP.≤-trans
      (mulRightNP y yNP (lowerSound xIn))
      (mulLeftNN (Eval.lower left) lNN (upperSound yIn))
  in liesIn
    (ℚP.≤-trans (min4BelowThird ll lu ul uu) lowerCorner)
    (ℚP.≤-trans upperCorner (secondBelowMax4 ll lu ul uu))
... | nonnegative lNN | straddlesZero rLowerNP rUpperNN =
  let
    ll = Eval.lower left * Eval.lower right
    lu = Eval.lower left * Eval.upper right
    ul = Eval.upper left * Eval.lower right
    uu = Eval.upper left * Eval.upper right
    xNN = ℚP.≤-trans lNN (lowerSound xIn)
    upperLNN = ℚP.≤-trans lNN (Eval.ordered left)
    lowerCorner : ul ≤ x * y
    lowerCorner = ℚP.≤-trans
      (mulRightNP (Eval.lower right) rLowerNP (upperSound xIn))
      (mulLeftNN x xNN (lowerSound yIn))
    upperCorner : x * y ≤ uu
    upperCorner = ℚP.≤-trans
      (mulLeftNN x xNN (upperSound yIn))
      (mulRightNN (Eval.upper right) rUpperNN (upperSound xIn))
  in liesIn
    (ℚP.≤-trans (min4BelowThird ll lu ul uu) lowerCorner)
    (ℚP.≤-trans upperCorner (fourthBelowMax4 ll lu ul uu))
... | nonpositive lNP | nonnegative rNN =
  let
    ll = Eval.lower left * Eval.lower right
    lu = Eval.lower left * Eval.upper right
    ul = Eval.upper left * Eval.lower right
    uu = Eval.upper left * Eval.upper right
    xNP = ℚP.≤-trans (upperSound xIn) lNP
    yNN = ℚP.≤-trans rNN (lowerSound yIn)
    lowerLNP = ℚP.≤-trans (Eval.ordered left) lNP
    upperRNN = ℚP.≤-trans rNN (Eval.ordered right)
    lowerCorner : lu ≤ x * y
    lowerCorner = ℚP.≤-trans
      (mulRightNN (Eval.upper right) upperRNN (lowerSound xIn))
      (mulLeftNP x xNP (upperSound yIn))
    upperCorner : x * y ≤ ul
    upperCorner = ℚP.≤-trans
      (mulRightNN y yNN (upperSound xIn))
      (mulLeftNP (Eval.upper left) lNP (lowerSound yIn))
  in liesIn
    (ℚP.≤-trans (min4BelowSecond ll lu ul uu) lowerCorner)
    (ℚP.≤-trans upperCorner (thirdBelowMax4 ll lu ul uu))
... | nonpositive lNP | nonpositive rNP =
  let
    ll = Eval.lower left * Eval.lower right
    lu = Eval.lower left * Eval.upper right
    ul = Eval.upper left * Eval.lower right
    uu = Eval.upper left * Eval.upper right
    xNP = ℚP.≤-trans (upperSound xIn) lNP
    yNP = ℚP.≤-trans (upperSound yIn) rNP
    lowerLNP = ℚP.≤-trans (Eval.ordered left) lNP
    lowerRNP = ℚP.≤-trans (Eval.ordered right) rNP
    lowerCorner : uu ≤ x * y
    lowerCorner = ℚP.≤-trans
      (mulRightNP (Eval.upper right) rNP (upperSound xIn))
      (mulLeftNP x xNP (upperSound yIn))
    upperCorner : x * y ≤ ll
    upperCorner = ℚP.≤-trans
      (mulRightNP y yNP (lowerSound xIn))
      (mulLeftNP (Eval.lower left) lowerLNP (lowerSound yIn))
  in liesIn
    (ℚP.≤-trans (min4BelowFourth ll lu ul uu) lowerCorner)
    (ℚP.≤-trans upperCorner (firstBelowMax4 ll lu ul uu))
... | nonpositive lNP | straddlesZero rLowerNP rUpperNN =
  let
    ll = Eval.lower left * Eval.lower right
    lu = Eval.lower left * Eval.upper right
    ul = Eval.upper left * Eval.lower right
    uu = Eval.upper left * Eval.upper right
    xNP = ℚP.≤-trans (upperSound xIn) lNP
    lowerLNP = ℚP.≤-trans (Eval.ordered left) lNP
    lowerCorner : lu ≤ x * y
    lowerCorner = ℚP.≤-trans
      (mulRightNN (Eval.upper right) rUpperNN (lowerSound xIn))
      (mulLeftNP x xNP (upperSound yIn))
    upperCorner : x * y ≤ ll
    upperCorner = ℚP.≤-trans
      (mulLeftNP x xNP (lowerSound yIn))
      (mulRightNP (Eval.lower right) rLowerNP (lowerSound xIn))
  in liesIn
    (ℚP.≤-trans (min4BelowSecond ll lu ul uu) lowerCorner)
    (ℚP.≤-trans upperCorner (firstBelowMax4 ll lu ul uu))
... | straddlesZero lLowerNP lUpperNN | nonnegative rNN =
  let
    ll = Eval.lower left * Eval.lower right
    lu = Eval.lower left * Eval.upper right
    ul = Eval.upper left * Eval.lower right
    uu = Eval.upper left * Eval.upper right
    yNN = ℚP.≤-trans rNN (lowerSound yIn)
    upperRNN = ℚP.≤-trans rNN (Eval.ordered right)
    lowerCorner : lu ≤ x * y
    lowerCorner = ℚP.≤-trans
      (mulLeftNP (Eval.lower left) lLowerNP (upperSound yIn))
      (mulRightNN y yNN (lowerSound xIn))
    upperCorner : x * y ≤ uu
    upperCorner = ℚP.≤-trans
      (mulRightNN y yNN (upperSound xIn))
      (mulLeftNN (Eval.upper left) lUpperNN (upperSound yIn))
  in liesIn
    (ℚP.≤-trans (min4BelowSecond ll lu ul uu) lowerCorner)
    (ℚP.≤-trans upperCorner (fourthBelowMax4 ll lu ul uu))
... | straddlesZero lLowerNP lUpperNN | nonpositive rNP =
  let
    ll = Eval.lower left * Eval.lower right
    lu = Eval.lower left * Eval.upper right
    ul = Eval.upper left * Eval.lower right
    uu = Eval.upper left * Eval.upper right
    yNP = ℚP.≤-trans (upperSound yIn) rNP
    lowerRNP = ℚP.≤-trans (Eval.ordered right) rNP
    lowerCorner : ul ≤ x * y
    lowerCorner = ℚP.≤-trans
      (mulLeftNN (Eval.upper left) lUpperNN (lowerSound yIn))
      (mulRightNP y yNP (upperSound xIn))
    upperCorner : x * y ≤ ll
    upperCorner = ℚP.≤-trans
      (mulRightNP y yNP (lowerSound xIn))
      (mulLeftNP (Eval.lower left) lLowerNP (lowerSound yIn))
  in liesIn
    (ℚP.≤-trans (min4BelowThird ll lu ul uu) lowerCorner)
    (ℚP.≤-trans upperCorner (firstBelowMax4 ll lu ul uu))
... | straddlesZero lLowerNP lUpperNN | straddlesZero rLowerNP rUpperNN
  with ℚP.≤-total 0ℚ x | ℚP.≤-total 0ℚ y
...   | inj₁ xNN | inj₁ yNN =
  let
    ll = Eval.lower left * Eval.lower right
    lu = Eval.lower left * Eval.upper right
    ul = Eval.upper left * Eval.lower right
    uu = Eval.upper left * Eval.upper right
    lowerToZero : lu ≤ 0ℚ
    lowerToZero = productNP (Eval.lower left) (Eval.upper right)
      lLowerNP rUpperNN
    zeroToProduct : 0ℚ ≤ x * y
    zeroToProduct = productNN x y xNN yNN
    upperCorner : x * y ≤ uu
    upperCorner = ℚP.≤-trans
      (mulRightNN y yNN (upperSound xIn))
      (mulLeftNN (Eval.upper left) lUpperNN (upperSound yIn))
  in liesIn
    (ℚP.≤-trans (min4BelowSecond ll lu ul uu)
      (ℚP.≤-trans lowerToZero zeroToProduct))
    (ℚP.≤-trans upperCorner (fourthBelowMax4 ll lu ul uu))
...   | inj₁ xNN | inj₂ yNP =
  let
    ll = Eval.lower left * Eval.lower right
    lu = Eval.lower left * Eval.upper right
    ul = Eval.upper left * Eval.lower right
    uu = Eval.upper left * Eval.upper right
    lowerCorner : ul ≤ x * y
    lowerCorner = ℚP.≤-trans
      (mulRightNP (Eval.lower right) rLowerNP (upperSound xIn))
      (mulLeftNN x xNN (lowerSound yIn))
    productToZero : x * y ≤ 0ℚ
    productToZero = productPN x y xNN yNP
    zeroToUpper : 0ℚ ≤ uu
    zeroToUpper = productNN (Eval.upper left) (Eval.upper right)
      lUpperNN rUpperNN
  in liesIn
    (ℚP.≤-trans (min4BelowThird ll lu ul uu) lowerCorner)
    (ℚP.≤-trans productToZero
      (ℚP.≤-trans zeroToUpper (fourthBelowMax4 ll lu ul uu)))
...   | inj₂ xNP | inj₁ yNN =
  let
    ll = Eval.lower left * Eval.lower right
    lu = Eval.lower left * Eval.upper right
    ul = Eval.upper left * Eval.lower right
    uu = Eval.upper left * Eval.upper right
    lowerCorner : lu ≤ x * y
    lowerCorner = ℚP.≤-trans
      (mulLeftNP (Eval.lower left) lLowerNP (upperSound yIn))
      (mulRightNN y yNN (lowerSound xIn))
    productToZero : x * y ≤ 0ℚ
    productToZero = productNP x y xNP yNN
    zeroToUpper : 0ℚ ≤ uu
    zeroToUpper = productNN (Eval.upper left) (Eval.upper right)
      lUpperNN rUpperNN
  in liesIn
    (ℚP.≤-trans (min4BelowSecond ll lu ul uu) lowerCorner)
    (ℚP.≤-trans productToZero
      (ℚP.≤-trans zeroToUpper (fourthBelowMax4 ll lu ul uu)))
...   | inj₂ xNP | inj₂ yNP =
  let
    ll = Eval.lower left * Eval.lower right
    lu = Eval.lower left * Eval.upper right
    ul = Eval.upper left * Eval.lower right
    uu = Eval.upper left * Eval.upper right
    lowerToZero : lu ≤ 0ℚ
    lowerToZero = productNP (Eval.lower left) (Eval.upper right)
      lLowerNP rUpperNN
    zeroToProduct : 0ℚ ≤ x * y
    zeroToProduct = productPP x y xNP yNP
    upperCorner : x * y ≤ ll
    upperCorner = ℚP.≤-trans
      (mulRightNP y yNP (lowerSound xIn))
      (mulLeftNP (Eval.lower left) lLowerNP (lowerSound yIn))
  in liesIn
    (ℚP.≤-trans (min4BelowSecond ll lu ul uu)
      (ℚP.≤-trans lowerToZero zeroToProduct))
    (ℚP.≤-trans upperCorner (firstBelowMax4 ll lu ul uu))

------------------------------------------------------------------------
-- Positive-denominator division.
------------------------------------------------------------------------

toQuotientSign : ∀ {lower upper} →
  IntervalSign lower upper → Quotient.NumeratorSignCase lower upper
toQuotientSign (nonnegative proof) = Quotient.numeratorNonnegative proof
toQuotientSign (nonpositive proof) = Quotient.numeratorNonpositive proof
toQuotientSign (straddlesZero lowerProof upperProof) =
  Quotient.numeratorStraddlesZero lowerProof upperProof

divideInterval :
  (numerator denominator : Eval.RationalInterval) →
  0ℚ < Eval.lower denominator → Eval.RationalInterval
divideInterval numerator denominator denominatorPositive =
  let
    signCase = toQuotientSign (intervalSign numerator)
    endpointOrder = Eval.ordered denominator
    lowerEndpoint = Quotient.quotientLowerEndpoint signCase
      (Eval.lower denominator) (Eval.upper denominator)
      denominatorPositive endpointOrder
    upperEndpoint = Quotient.quotientUpperEndpoint signCase
      (Eval.lower denominator) (Eval.upper denominator)
      denominatorPositive endpointOrder
    chosen = Quotient.positiveDenominatorQuotientEnclosure
      signCase denominatorPositive endpointOrder
      ℚP.≤-refl (Eval.ordered numerator)
      ℚP.≤-refl (Eval.ordered denominator)
  in
  Eval.interval lowerEndpoint upperEndpoint
    (ℚP.≤-trans
      (Quotient.lowerSound chosen)
      (Quotient.upperSound chosen))

divideIntervalSound :
  ∀ {numeratorValue denominatorValue numerator denominator}
    (numeratorIn : LiesIn numeratorValue numerator)
    (denominatorIn : LiesIn denominatorValue denominator)
    (denominatorPositive : 0ℚ < Eval.lower denominator) →
  let actualPositive =
        ℚP.<-≤-trans denominatorPositive (lowerSound denominatorIn)
  in
  LiesIn
    (Quotient.dividePositive numeratorValue denominatorValue actualPositive)
    (divideInterval numerator denominator denominatorPositive)
divideIntervalSound {numeratorValue} {denominatorValue} {numerator} {denominator}
    numeratorIn denominatorIn denominatorPositive =
  let
    actualPositive =
      ℚP.<-≤-trans denominatorPositive (lowerSound denominatorIn)
    quotientSound = Quotient.positiveDenominatorQuotientEnclosure
      (toQuotientSign (intervalSign numerator))
      denominatorPositive (Eval.ordered denominator)
      (lowerSound numeratorIn) (upperSound numeratorIn)
      (lowerSound denominatorIn) (upperSound denominatorIn)
  in
  liesIn
    (Quotient.lowerSound quotientSound)
    (Quotient.upperSound quotientSound)

------------------------------------------------------------------------
-- Inductive expression derivations.
------------------------------------------------------------------------

data ExpressionInterval
    (atomBoxes : Eval.TrigAtom → Eval.RationalInterval) :
    Eval.DiagramExpression → Eval.RationalInterval → Set where
  constant : ∀ value →
    ExpressionInterval atomBoxes
      (Eval.rationalConstant value) (constantInterval value)

  trig : ∀ trigAtom →
    ExpressionInterval atomBoxes
      (Eval.atom trigAtom) (atomBoxes trigAtom)

  plus : ∀ {leftExpr rightExpr leftBox rightBox} →
    ExpressionInterval atomBoxes leftExpr leftBox →
    ExpressionInterval atomBoxes rightExpr rightBox →
    ExpressionInterval atomBoxes
      (Eval.add leftExpr rightExpr) (addInterval leftBox rightBox)

  minus : ∀ {leftExpr rightExpr leftBox rightBox} →
    ExpressionInterval atomBoxes leftExpr leftBox →
    ExpressionInterval atomBoxes rightExpr rightBox →
    ExpressionInterval atomBoxes
      (Eval.subtract leftExpr rightExpr) (subtractInterval leftBox rightBox)

  times : ∀ {leftExpr rightExpr leftBox rightBox} →
    ExpressionInterval atomBoxes leftExpr leftBox →
    ExpressionInterval atomBoxes rightExpr rightBox →
    ExpressionInterval atomBoxes
      (Eval.multiply leftExpr rightExpr) (multiplyInterval leftBox rightBox)

  quotient : ∀ {numeratorExpr denominatorExpr numeratorBox denominatorBox} →
    (numeratorDerivation :
      ExpressionInterval atomBoxes numeratorExpr numeratorBox) →
    (denominatorDerivation :
      ExpressionInterval atomBoxes denominatorExpr denominatorBox) →
    (denominatorPositive : 0ℚ < Eval.lower denominatorBox) →
    ExpressionInterval atomBoxes
      (Eval.divide numeratorExpr denominatorExpr)
      (divideInterval numeratorBox denominatorBox denominatorPositive)

  negative : ∀ {expression box} →
    ExpressionInterval atomBoxes expression box →
    ExpressionInterval atomBoxes
      (Eval.negate expression) (negateInterval box)

record EvaluatedValue (box : Eval.RationalInterval) : Set where
  constructor evaluated
  field
    value : ℚ
    inside : LiesIn value box
open EvaluatedValue public

evaluateDerivation :
  ∀ {atomBoxes expression box} →
  (atomValue : Eval.TrigAtom → ℚ) →
  (atomSound : ∀ trigAtom → LiesIn (atomValue trigAtom) (atomBoxes trigAtom)) →
  ExpressionInterval atomBoxes expression box →
  EvaluatedValue box
evaluateDerivation atomValue atomSound (constant scalar) =
  evaluated scalar (liesIn ℚP.≤-refl ℚP.≤-refl)
evaluateDerivation atomValue atomSound (trig trigAtom) =
  evaluated (atomValue trigAtom) (atomSound trigAtom)
evaluateDerivation atomValue atomSound (plus left right) =
  let
    leftResult = evaluateDerivation atomValue atomSound left
    rightResult = evaluateDerivation atomValue atomSound right
  in
  evaluated
    (value leftResult + value rightResult)
    (addIntervalSound (inside leftResult) (inside rightResult))
evaluateDerivation atomValue atomSound (minus left right) =
  let
    leftResult = evaluateDerivation atomValue atomSound left
    rightResult = evaluateDerivation atomValue atomSound right
  in
  evaluated
    (value leftResult - value rightResult)
    (subtractIntervalSound (inside leftResult) (inside rightResult))
evaluateDerivation atomValue atomSound (times left right) =
  let
    leftResult = evaluateDerivation atomValue atomSound left
    rightResult = evaluateDerivation atomValue atomSound right
  in
  evaluated
    (value leftResult * value rightResult)
    (multiplyIntervalSound (inside leftResult) (inside rightResult))
evaluateDerivation atomValue atomSound
    (quotient numerator denominator denominatorPositive) =
  let
    numeratorResult = evaluateDerivation atomValue atomSound numerator
    denominatorResult = evaluateDerivation atomValue atomSound denominator
    actualPositive = ℚP.<-≤-trans denominatorPositive
      (lowerSound (inside denominatorResult))
  in
  evaluated
    (Quotient.dividePositive
      (value numeratorResult) (value denominatorResult) actualPositive)
    (divideIntervalSound
      (inside numeratorResult) (inside denominatorResult) denominatorPositive)
evaluateDerivation atomValue atomSound (negative expression) =
  let result = evaluateDerivation atomValue atomSound expression
  in evaluated (- value result) (negateIntervalSound (inside result))

rationalIntervalAddSubtractNegateSoundLevel : ProofLevel
rationalIntervalAddSubtractNegateSoundLevel = machineChecked

rationalIntervalFourCornerMultiplySoundLevel : ProofLevel
rationalIntervalFourCornerMultiplySoundLevel = machineChecked

rationalIntervalPositiveDivisionSoundLevel : ProofLevel
rationalIntervalPositiveDivisionSoundLevel = machineChecked

typedDiagramExpressionRecursiveSoundnessLevel : ProofLevel
typedDiagramExpressionRecursiveSoundnessLevel = machineChecked
