module DASHI.Physics.Closure.NSTriadKNR567ToLiteralR571M2Exact where

------------------------------------------------------------------------
-- PERIODIC B / R567 FULL SQUARE -> LITERAL R571 SECOND MOMENT
--
-- For the complete R567 ordered square on one fixed output, assign to each
-- literal cell (alpha,beta) its SAME-OBJECT preferred R571 second-moment
-- sample.  If the literal forcing cell is bounded by that sample's paired
-- magnitude, then the preferred one-sided pointwise theorem gives
--
--   forcingCell(alpha,beta)
--     <= C * weightedSecondMoment(cellToSample alpha beta),
--
-- where C = A1 G2 + A2 G1.  Finite full-square monotonicity and exact scalar
-- factorization then give the complete square bound with NO cardinality loss.
--
-- Thus the only representation debt remaining here is the actual R567-cell
-- -> R571-sample map plus its literal pointwise forcing inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment
import DASHI.Physics.Closure.NSTriadKNR571PreferredOneSidedSecondMomentExact as Preferred

fullSquareMonotone :
  ∀ {A : Set}
    (items : List A)
    (lower upper : A → A → ℚ) →
  ((x y : A) → lower x y ≤ upper x y) →
  R543.fullSquareSum lower items ≤ R543.fullSquareSum upper items
fullSquareMonotone [] lower upper pointwise = ℚP.≤-refl
fullSquareMonotone (x ∷ xs) lower upper pointwise =
  ℚP.+-mono-≤
    (pointwise x x)
    (ℚP.+-mono-≤
      (rowMonotone x xs)
      (ℚP.+-mono-≤
        (columnMonotone xs x)
        (fullSquareMonotone xs lower upper pointwise)))
  where
  rowMonotone :
    (x : A) (ys : List A) →
    R543.rowSum lower x ys ≤ R543.rowSum upper x ys
  rowMonotone x [] = ℚP.≤-refl
  rowMonotone x (y ∷ ys) =
    ℚP.+-mono-≤ (pointwise x y) (rowMonotone x ys)

  columnMonotone :
    (ys : List A) (x : A) →
    R543.columnSum lower ys x ≤ R543.columnSum upper ys x
  columnMonotone [] x = ℚP.≤-refl
  columnMonotone (y ∷ ys) x =
    ℚP.+-mono-≤ (pointwise y x) (columnMonotone ys x)

rowScale :
  ∀ {A : Set}
    (scale : ℚ)
    (value : A → A → ℚ)
    (x : A)
    (items : List A) →
  R543.rowSum (λ a b → scale * value a b) x items
  ≡ scale * R543.rowSum value x items
rowScale scale value x [] = solve (scale ∷ [])
rowScale scale value x (y ∷ ys)
  rewrite rowScale scale value x ys =
  solve (scale ∷ value x y ∷ R543.rowSum value x ys ∷ [])

columnScale :
  ∀ {A : Set}
    (scale : ℚ)
    (value : A → A → ℚ)
    (items : List A)
    (x : A) →
  R543.columnSum (λ a b → scale * value a b) items x
  ≡ scale * R543.columnSum value items x
columnScale scale value [] x = solve (scale ∷ [])
columnScale scale value (y ∷ ys) x
  rewrite columnScale scale value ys x =
  solve (scale ∷ value y x ∷ R543.columnSum value ys x ∷ [])

fullSquareScale :
  ∀ {A : Set}
    (scale : ℚ)
    (value : A → A → ℚ)
    (items : List A) →
  R543.fullSquareSum (λ a b → scale * value a b) items
  ≡ scale * R543.fullSquareSum value items
fullSquareScale scale value [] = solve (scale ∷ [])
fullSquareScale scale value (x ∷ xs)
  rewrite rowScale scale value x xs
        | columnScale scale value xs x
        | fullSquareScale scale value xs =
  solve
    ( scale
    ∷ value x x
    ∷ R543.rowSum value x xs
    ∷ R543.columnSum value xs x
    ∷ R543.fullSquareSum value xs
    ∷ [])

record LiteralR567R571Correspondence (A : Set) : Set₁ where
  field
    items : List A
    forcingCell : A → A → ℚ
    cellToSample : A → A → Moment.PairedSecondMomentSample

    preferredBudget : Preferred.PreferredOneSidedSecondMomentBudget

    sampleInPreferredBudget :
      (x y : A) →
      x ∈ items →
      y ∈ items →
      cellToSample x y ∈ Preferred.samples preferredBudget

    forcingCellBelowPairedMagnitude :
      (x y : A) →
      forcingCell x y
      ≤ Moment.pairedMagnitude (cellToSample x y)

    -- Membership of x,y in the literal output fibre is not needed by the
    -- pointwise inequality itself, but is retained above so the actual physical
    -- specialization cannot silently map cells outside the selected family.
    pointwisePreferredBound :
      (x y : A) →
      Moment.pairedMagnitude (cellToSample x y)
      ≤ Preferred.preferredCoefficient preferredBudget
          * Moment.weightedSecondMoment (cellToSample x y)

open LiteralR567R571Correspondence public

literalM2Cell :
  ∀ {A} →
  LiteralR567R571Correspondence A →
  A → A → ℚ
literalM2Cell C x y =
  Moment.weightedSecondMoment (cellToSample C x y)

r567CellBelowPreferredR571M2 :
  ∀ {A} →
  (C : LiteralR567R571Correspondence A) →
  (x y : A) →
  forcingCell C x y
  ≤ Preferred.preferredCoefficient (preferredBudget C)
      * literalM2Cell C x y
r567CellBelowPreferredR571M2 C x y =
  ℚP.≤-trans
    (forcingCellBelowPairedMagnitude C x y)
    (pointwisePreferredBound C x y)

r567FullSquareBelowPreferredR571M2 :
  ∀ {A} →
  (C : LiteralR567R571Correspondence A) →
  R543.fullSquareSum (forcingCell C) (items C)
  ≤ Preferred.preferredCoefficient (preferredBudget C)
      * R543.fullSquareSum (literalM2Cell C) (items C)
r567FullSquareBelowPreferredR571M2 C =
  let
    pointwiseScaled :
      R543.fullSquareSum (forcingCell C) (items C)
      ≤
      R543.fullSquareSum
        (λ x y →
          Preferred.preferredCoefficient (preferredBudget C)
            * literalM2Cell C x y)
        (items C)
    pointwiseScaled =
      fullSquareMonotone
        (items C)
        (forcingCell C)
        (λ x y →
          Preferred.preferredCoefficient (preferredBudget C)
            * literalM2Cell C x y)
        (r567CellBelowPreferredR571M2 C)

    factor =
      fullSquareScale
        (Preferred.preferredCoefficient (preferredBudget C))
        (literalM2Cell C)
        (items C)
  in
  subst
    (λ upper →
      R543.fullSquareSum (forcingCell C) (items C) ≤ upper)
    factor
    pointwiseScaled

r567CompleteSquareAggregationClosed : Bool
r567CompleteSquareAggregationClosed = true

r567CellToLiteralR571SampleSameObjectClosedHere : Bool
r567CellToLiteralR571SampleSameObjectClosedHere = false

r567CellBelowLiteralR571PairedMagnitudeClosedHere : Bool
r567CellBelowLiteralR571PairedMagnitudeClosedHere = false

preferredPointwiseEnvelopeSpecializedToLiteralFamilyHere : Bool
preferredPointwiseEnvelopeSpecializedToLiteralFamilyHere = false

clayPromotion : Bool
clayPromotion = false

r567CompleteSquareAggregationClosedIsTrue :
  r567CompleteSquareAggregationClosed ≡ true
r567CompleteSquareAggregationClosedIsTrue = refl
