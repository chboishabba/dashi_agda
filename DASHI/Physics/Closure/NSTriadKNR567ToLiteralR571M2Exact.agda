module DASHI.Physics.Closure.NSTriadKNR567ToLiteralR571M2Exact where

------------------------------------------------------------------------
-- PERIODIC B / R567 FULL SQUARE -> LITERAL R571 SECOND MOMENT
--
-- This is the finite theorem the live B route actually needs.
--
-- For the complete R567 ordered square on one fixed output, suppose each
-- literal pair (alpha,beta) is assigned its SAME-OBJECT preferred R571
-- PairedSecondMomentSample, and the R567 forcing cell is bounded by that
-- sample's paired magnitude.  Then the already-proved preferred one-sided
-- second-moment theorem sums over the COMPLETE ordered square with no
-- cardinality factor.
--
-- The only remaining representation debt after this module is the concrete
-- cellToSample map and its pointwise same-object inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; here; there)
open import Data.Rational.Base using (ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCenteredCommutatorBudgetExact as Sum
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment
import DASHI.Physics.Closure.NSTriadKNR571PreferredOneSidedSecondMomentExact as Preferred

orderedPairSamples :
  ∀ {A : Set} →
  List A →
  (A → A → Moment.PairedSecondMomentSample) →
  List Moment.PairedSecondMomentSample
orderedPairSamples [] sample = []
orderedPairSamples (x ∷ xs) sample =
  sample x x
  ∷ appendRow x xs sample
  where
  appendRow :
    A →
    List A →
    (A → A → Moment.PairedSecondMomentSample) →
    List Moment.PairedSecondMomentSample
  appendRow x [] sample = orderedPairSamples xs sample
  appendRow x (y ∷ ys) sample =
    sample x y ∷ sample y x ∷ appendRow x ys sample

sampleMagnitude :
  ∀ {A : Set} →
  (A → A → Moment.PairedSecondMomentSample) →
  A → A → ℚ
sampleMagnitude sample x y = Moment.pairedMagnitude (sample x y)

sampleSecondMoment :
  ∀ {A : Set} →
  (A → A → Moment.PairedSecondMomentSample) →
  A → A → ℚ
sampleSecondMoment sample x y = Moment.weightedSecondMoment (sample x y)

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

fullSquareSampleMagnitudeIsSum :
  ∀ {A : Set}
    (items : List A)
    (sample : A → A → Moment.PairedSecondMomentSample) →
  R543.fullSquareSum (sampleMagnitude sample) items
  ≡ Sum.sumBy (orderedPairSamples items sample) Moment.pairedMagnitude
fullSquareSampleMagnitudeIsSum [] sample = refl
fullSquareSampleMagnitudeIsSum (x ∷ xs) sample = refl

fullSquareSampleSecondMomentIsSum :
  ∀ {A : Set}
    (items : List A)
    (sample : A → A → Moment.PairedSecondMomentSample) →
  R543.fullSquareSum (sampleSecondMoment sample) items
  ≡ Sum.sumBy (orderedPairSamples items sample) Moment.weightedSecondMoment
fullSquareSampleSecondMomentIsSum [] sample = refl
fullSquareSampleSecondMomentIsSum (x ∷ xs) sample = refl

record LiteralR567R571Correspondence (A : Set) : Set₁ where
  field
    items : List A
    forcingCell : A → A → ℚ
    cellToSample : A → A → Moment.PairedSecondMomentSample

    preferredBudget : Preferred.PreferredOneSidedSecondMomentBudget

    allOrderedSamplesInBudget :
      (x y : A) →
      x ∈ items →
      y ∈ items →
      cellToSample x y ∈ Preferred.samples preferredBudget

    forcingCellBelowPairedMagnitude :
      (x y : A) →
      forcingCell x y
      ≤ Moment.pairedMagnitude (cellToSample x y)

open LiteralR567R571Correspondence public

-- Complete ordered-square bound.  This theorem is independent of any fibre
-- cardinality and retains the preferred one-sided coefficient.
r567FullSquareBelowPreferredR571M2 :
  ∀ {A} →
  (C : LiteralR567R571Correspondence A) →
  R543.fullSquareSum (forcingCell C) (items C)
  ≤ Preferred.preferredCoefficient (preferredBudget C)
      * R543.fullSquareSum
          (sampleSecondMoment (cellToSample C))
          (items C)
r567FullSquareBelowPreferredR571M2 C =
  let
    first :
      R543.fullSquareSum (forcingCell C) (items C)
      ≤ R543.fullSquareSum
          (sampleMagnitude (cellToSample C))
          (items C)
    first =
      fullSquareMonotone
        (items C)
        (forcingCell C)
        (sampleMagnitude (cellToSample C))
        (forcingCellBelowPairedMagnitude C)

    second :
      R543.fullSquareSum
        (sampleMagnitude (cellToSample C))
        (items C)
      ≤ Preferred.preferredCoefficient (preferredBudget C)
          * R543.fullSquareSum
              (sampleSecondMoment (cellToSample C))
              (items C)
    second =
      -- The preferred finite-family theorem applies to exactly the ordered
      -- pair list generated by the complete R567 square.
      let
        family = orderedPairSamples (items C) (cellToSample C)

        included :
          (s : Moment.PairedSecondMomentSample) →
          s ∈ family →
          s ∈ Preferred.samples (preferredBudget C)
        included s member =
          orderedMembershipToBudget
            (items C) (cellToSample C)
            (preferredBudget C)
            (allOrderedSamplesInBudget C)
            s member

        raw =
          Preferred.preferredSumBoundOn
            (preferredBudget C) family included
      in
      subst
        (λ lhs →
          lhs ≤ Preferred.preferredCoefficient (preferredBudget C)
            * R543.fullSquareSum
                (sampleSecondMoment (cellToSample C))
                (items C))
        (sym (fullSquareSampleMagnitudeIsSum
          (items C) (cellToSample C)))
        (subst
          (λ rhs →
            Sum.sumBy family Moment.pairedMagnitude
            ≤ Preferred.preferredCoefficient (preferredBudget C) * rhs)
          (sym (fullSquareSampleSecondMomentIsSum
            (items C) (cellToSample C)))
          raw)
  in
  ℚP.≤-trans first second

-- Membership inversion for the concrete ordered square.
orderedMembershipToBudget :
  ∀ {A}
    (items : List A)
    (sample : A → A → Moment.PairedSecondMomentSample)
    (budget : Preferred.PreferredOneSidedSecondMomentBudget) →
  ((x y : A) → x ∈ items → y ∈ items →
    sample x y ∈ Preferred.samples budget) →
  (s : Moment.PairedSecondMomentSample) →
  s ∈ orderedPairSamples items sample →
  s ∈ Preferred.samples budget
orderedMembershipToBudget [] sample budget pointwise s ()
orderedMembershipToBudget (x ∷ xs) sample budget pointwise s member =
  orderedMembershipStep x xs sample budget pointwise s member
  where
  orderedMembershipStep :
    (x : A) (xs : List A)
    (sample : A → A → Moment.PairedSecondMomentSample)
    (budget : Preferred.PreferredOneSidedSecondMomentBudget) →
    ((a b : A) → a ∈ (x ∷ xs) → b ∈ (x ∷ xs) →
      sample a b ∈ Preferred.samples budget) →
    (s : Moment.PairedSecondMomentSample) →
    s ∈ orderedPairSamples (x ∷ xs) sample →
    s ∈ Preferred.samples budget
  orderedMembershipStep x xs sample budget pointwise .(sample x x) (here refl) =
    pointwise x x (here refl) (here refl)
  orderedMembershipStep x xs sample budget pointwise s (there rest) =
    tailMembership x xs sample budget pointwise s rest

  tailMembership :
    (x : A) (xs : List A)
    (sample : A → A → Moment.PairedSecondMomentSample)
    (budget : Preferred.PreferredOneSidedSecondMomentBudget) →
    ((a b : A) → a ∈ (x ∷ xs) → b ∈ (x ∷ xs) →
      sample a b ∈ Preferred.samples budget) →
    (s : Moment.PairedSecondMomentSample) →
    s ∈ appendRow x xs sample →
    s ∈ Preferred.samples budget
  tailMembership x [] sample budget pointwise s member =
    orderedMembershipToBudget [] sample budget
      (λ a b () _) s member
  tailMembership x (y ∷ ys) sample budget pointwise .(sample x y) (here refl) =
    pointwise x y (here refl) (there (here refl))
  tailMembership x (y ∷ ys) sample budget pointwise s (there (here refl)) =
    pointwise y x (there (here refl)) (here refl)
  tailMembership x (y ∷ ys) sample budget pointwise s (there (there rest)) =
    tailMembership x ys sample budget
      (λ a b ha hb → pointwise a b ha hb)
      s rest

r567CompleteSquareAggregationClosed : Bool
r567CompleteSquareAggregationClosed = true

r567CellToLiteralR571SampleSameObjectClosedHere : Bool
r567CellToLiteralR571SampleSameObjectClosedHere = false

r567CellBelowLiteralR571PairedMagnitudeClosedHere : Bool
r567CellBelowLiteralR571PairedMagnitudeClosedHere = false

clayPromotion : Bool
clayPromotion = false

r567CompleteSquareAggregationClosedIsTrue :
  r567CompleteSquareAggregationClosed ≡ true
r567CompleteSquareAggregationClosedIsTrue = refl
