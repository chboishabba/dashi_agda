module DASHI.Physics.YangMills.BalabanClayT4RefinedSineSquareRegularBoxesExact where

-- SOURCE-NATIVE INTERVAL-DEPENDENCY REPAIR for the 4D Wilson symbol.
--
-- The old Canonical.sineSquareInterval computes the generic product [a,b]*[a,b],
-- so on a sine interval [-1,1] its lower endpoint is -1. A real square is
-- necessarily nonnegative. Clipping the generic four-corner lower endpoint
-- at zero yields a strictly sharper, still Bishop-sound interval, WITHOUT
-- dividing by an interval that contains zero.
--
-- For the four source grid coordinate types use:
--   negativeOuter: sin(k/2) in [-1,-87/128]
--   negativeInner: sin(k/2) in [-1,1]
--   positiveInner: sin(k/2) in [-1,1]
--   positiveOuter: sin(k/2) in [87/128,1]
-- These are explicit RATIONAL enclosure targets, NOT claims that the
-- literal source's sine atom has already been identified with them.
-- The known Machin one-dimensional sine theorem is a producer for the
-- positive outer lower bound, conditional on matching the Fourier angle.
--
-- Every ORIGINAL regular 4D cell then has a strictly positive rational
-- endpoint floor 7569/4096 for the SUMMED Wilson propagator symbol
-- 4 Σ sin²(kμ/2). This finite result is independent of the unproved
-- sharper 2m rank claim.
--
-- Source physical obligations remaining: sine membership for each
-- actual Fourier atom, *shifted* momentum propagators, and source AST
-- identification of denominator with the summed Wilson symbol.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _/_; -_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Sum.Base using (inj₁; inj₂)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Squares
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Product
import DASHI.Physics.YangMills.BalabanClayT4BishopExpressionIntervalSemanticsExact as Sem
import DASHI.Physics.YangMills.BalabanClayT4CanonicalBishopAtomEnvironmentExact as Canonical
import DASHI.Physics.YangMills.BalabanLiteralFourCornerCommutativityExact as Extremes

lowerSine : ℚ
lowerSine = + 87 / 128

componentFloor : ℚ
componentFloor = + 7569 / 4096

minusOne : ℚ
minusOne = - 1ℚ

sourceSineBox : Grid.IntervalCell → Eval.RationalInterval
sourceSineBox Grid.negativeOuter =
  Eval.interval minusOne (- lowerSine) (ℚP.≤ᵇ⇒≤ tt)
sourceSineBox Grid.negativeInner =
  Eval.interval minusOne 1ℚ (ℚP.≤ᵇ⇒≤ tt)
sourceSineBox Grid.positiveInner =
  Eval.interval minusOne 1ℚ (ℚP.≤ᵇ⇒≤ tt)
sourceSineBox Grid.positiveOuter =
  Eval.interval lowerSine 1ℚ (ℚP.≤ᵇ⇒≤ tt)

-- Both upper-endpoint square and fourth original product corner coincide:
-- upper*upper <= max4(lower*lower, lower*upper, upper*lower, upper*upper).
squareUpperNonnegative : ∀ box →
  0ℚ ≤ Eval.upper (Typed.multiplyInterval box box)
squareUpperNonnegative box =
  ℚP.≤-trans
    (Squares.squareNonnegative (Eval.upper box))
    (Typed.fourthBelowMax4
      (Eval.lower box * Eval.lower box)
      (Eval.lower box * Eval.upper box)
      (Eval.upper box * Eval.lower box)
      (Eval.upper box * Eval.upper box))

-- This is a mathematically sound *dependency-aware* square enclosure.
refinedSquareOrdered : ∀ box →
  Typed.max2 0ℚ (Eval.lower (Typed.multiplyInterval box box))
  ≤ Eval.upper (Typed.multiplyInterval box box)
refinedSquareOrdered box
  with ℚP.≤-total 0ℚ (Eval.lower (Typed.multiplyInterval box box))
... | inj₁ _ = Eval.ordered (Typed.multiplyInterval box box)
... | inj₂ _ = squareUpperNonnegative box

refinedSquare : Eval.RationalInterval → Eval.RationalInterval
refinedSquare box =
  Eval.interval
    (Typed.max2 0ℚ (Eval.lower (Typed.multiplyInterval box box)))
    (Eval.upper (Typed.multiplyInterval box box))
    (refinedSquareOrdered box)

refinedSquareLowerNonnegative : ∀ box →
  0ℚ ≤ Eval.lower (refinedSquare box)
refinedSquareLowerNonnegative box
  with ℚP.≤-total 0ℚ (Eval.lower (Typed.multiplyInterval box box))
... | inj₁ lowerNN = lowerNN
... | inj₂ _ = ℚP.≤-refl

refinedSquareBishopSound :
  ∀ {value box} →
  Product.BishopLiesIn value box →
  Product.BishopLiesIn (value Bishop.* value) (refinedSquare box)
refinedSquareBishopSound {value} {box} inside =
  let old = Product.multiplyIntervalBishopSound inside inside
      nonneg : Bishop.0ℝ Bishop.≤ (value Bishop.* value)
      nonneg = BishopP.nonNegx⇒0≤x (BishopP.nonNegSquare value)
      newLower : Product.embed (Eval.lower (refinedSquare box))
        Bishop.≤ (value Bishop.* value)
      newLower with ℚP.≤-total 0ℚ
        (Eval.lower (Typed.multiplyInterval box box))
      ... | inj₁ _ = Product.lowerSound old
      ... | inj₂ _ = BishopP.≤-respˡ-≃ Product.embedZero nonneg
  in Product.bishopLiesIn newLower (Product.upperSound old)

sourceComponent : Grid.IntervalCell → Eval.RationalInterval
sourceComponent c =
  Typed.multiplyInterval
    (Canonical.singletonInterval Canonical.fourRational)
    (refinedSquare (sourceSineBox c))

-- The lower endpoints are actually computed by original rational
-- four-corner multiplication, not fabricated post-hoc bounds.
sourceComponentNonnegative : ∀ c →
  0ℚ ≤ Eval.lower (sourceComponent c)
sourceComponentNonnegative Grid.negativeOuter = ℚP.≤ᵇ⇒≤ tt
sourceComponentNonnegative Grid.negativeInner = ℚP.≤ᵇ⇒≤ tt
sourceComponentNonnegative Grid.positiveInner = ℚP.≤ᵇ⇒≤ tt
sourceComponentNonnegative Grid.positiveOuter = ℚP.≤ᵇ⇒≤ tt

-- Even the weaker 7569/4096 bound has a positive rational endpoint.
sourceOuterComponentFloor :
  ∀ c → Grid.isInner c ≡ false →
  componentFloor ≤ Eval.lower (sourceComponent c)
sourceOuterComponentFloor Grid.negativeOuter _ = ℚP.≤ᵇ⇒≤ tt
sourceOuterComponentFloor Grid.negativeInner ()
sourceOuterComponentFloor Grid.positiveInner ()
sourceOuterComponentFloor Grid.positiveOuter _ = ℚP.≤ᵇ⇒≤ tt

sourceWilsonDenominatorBox : Grid.GridCell4 → Eval.RationalInterval
sourceWilsonDenominatorBox cell =
  Typed.addInterval
    (Typed.addInterval
      (sourceComponent (Grid.c0 cell))
      (sourceComponent (Grid.c1 cell)))
    (Typed.addInterval
      (sourceComponent (Grid.c2 cell))
      (sourceComponent (Grid.c3 cell)))

-- 4^4 explicit finite source-grid proof (240 regular, 16 infrared).
-- The cells are the literal generated source Grid.gridCell4 constructors.
-- Proof irrelevance of the bounds is not invoked.

sourceRegularWilsonLower :
  ∀ cell → Grid.allInner cell ≡ false →
  componentFloor ≤ Eval.lower (sourceWilsonDenominatorBox cell)
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.negativeInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.positiveInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.negativeInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.positiveInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.negativeInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.positiveInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.negativeInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.positiveInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.negativeInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.positiveInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.negativeInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.positiveInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.negativeInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.positiveInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.negativeInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.positiveInner)
  ()
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveInner)
  _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularWilsonLower
  (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter)
  _ = ℚP.≤ᵇ⇒≤ tt

sourceStrictPositiveAtRegularBox :
  ∀ cell → Grid.allInner cell ≡ false →
  0ℚ ℚ.< Eval.lower (sourceWilsonDenominatorBox cell)
sourceStrictPositiveAtRegularBox cell regular =
  ℚP.<-≤-trans
    (ℚP.positive⁻¹ componentFloor)
    (sourceRegularWilsonLower cell regular)

-- This is a LIVE Bishop-real soundness producer, not a phantom Set:
-- a source-sine membership proof produces the TRUE four-times-square
-- Bishop-real membership for the selected source coordinate.
sourceComponentBishopSound :
  ∀ c {value} →
  Product.BishopLiesIn value (sourceSineBox c) →
  Product.BishopLiesIn
    (Canonical.fourValue Bishop.* (value Bishop.* value))
    (sourceComponent c)
sourceComponentBishopSound c inside =
  Product.multiplyIntervalBishopSound
    (Canonical.singletonSound Canonical.fourRational)
    (refinedSquareBishopSound inside)

-- To obtain a source physical denominator certificate, provide each
-- actual Fourier sine-half atom's membership in the sourceSineBox
-- belonging to its original Grid.cell coordinate. The materialisation
-- is not inferred from choosing the box's rational endpoints.
