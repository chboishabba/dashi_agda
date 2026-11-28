module DASHI.Foundations.BishopFiniteFilteredCellSumExact where

-- Finite positive filtered-cell majorant. The filter is represented
-- by the actual decidable predicate; rejected cells contribute zero.
-- No convergence or division by the majorant is needed.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Nullary using (Dec; yes; no)
import Data.Nat.Base as N
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Foundations.BishopFiniteRectangleInsideCauchyTriangleExact as Rect

masked : (S : Nat → Set) → (∀ i → Dec (S i)) →
  (Nat → R.ℝ) → Nat → R.ℝ
masked S decide f i with decide i
... | yes _ = f i
... | no _ = R.0ℝ

maskedCellBound :
  ∀ (S : Nat → Set) (decide : ∀ i → Dec (S i))
    (f g : Nat → R.ℝ) →
  (∀ i → R.NonNegative (g i)) →
  (∀ i → S i → R._≤_ (f i) (g i)) →
  ∀ i → R._≤_ (masked S decide f i) (g i)
maskedCellBound S decide f g hg h i with decide i
... | yes p = h i p
... | no _ = P.nonNegx⇒0≤x (hg i)

maskedFiniteSumBound :
  ∀ (S : Nat → Set) (decide : ∀ i → Dec (S i))
    (f g : Nat → R.ℝ) →
  (∀ i → R.NonNegative (g i)) →
  (∀ i → S i → R._≤_ (f i) (g i)) →
  ∀ count →
  R._≤_ (Seq.SeriesOf (masked S decide f) count)
        (Seq.SeriesOf g count)
maskedFiniteSumBound S decide f g hg h count =
  Rect.finitePointwiseBound count
    (λ i _ → maskedCellBound S decide f g hg h i)

-- Nested original Nat-prefix sums, not a cardinality estimate.
maskedRectangleBound :
  ∀ (S : Nat → Nat → Set) (decide : ∀ i j → Dec (S i j))
    (f g : Nat → Nat → R.ℝ) →
  (∀ i j → R.NonNegative (g i j)) →
  (∀ i j → S i j → R._≤_ (f i j) (g i j)) →
  ∀ height width →
  R._≤_
    (Seq.SeriesOf
      (λ i → Seq.SeriesOf (masked (S i) (decide i) (f i)) width)
      height)
    (Seq.SeriesOf (λ i → Seq.SeriesOf (g i) width) height)
maskedRectangleBound S decide f g hg h height width =
  Rect.finitePointwiseBound height
    (λ i _ → maskedFiniteSumBound (S i) (decide i)
      (f i) (g i) (hg i) (h i) width)
