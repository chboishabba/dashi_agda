module DASHI.Physics.YangMills.BalabanClayT4RegularGridMomentumGapExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721.
--
-- DASHI CONTRIBUTION
--
-- The generated 4^4 Brillouin partition removes exactly the 2^4 cells whose
-- four normalized coordinates lie in [-1/2,1/2].  Hence every one of the 240
-- regular cells has a coordinate in [-1,-1/2] or [1/2,1].  This file proves
-- that fact from the literal Grid.allInner classifier and converts it into the
-- exact rational geometric gap
--
--     x0^2 + x1^2 + x2^2 + x3^2 >= 1/4
--
-- for every point of every regular cell.  No per-box positivity receipt is
-- accepted.  This is the finite geometric input required before transferring
-- the gap through k_mu = pi x_mu and hat{k}_mu = 2 sin(k_mu/2).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; -_; _*_; _≤_; _≤ᵇ_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (sym; trans; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Interval
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2

half quarter : ℚ
half = + 1 / 2
quarter = + 1 / 4

halfNonnegative : 0ℚ ≤ half
halfNonnegative = ℚP.≤ᵇ⇒≤ tt

halfSquareQuarter : half * half ≡ quarter
halfSquareQuarter = ℚRing.solve-∀

------------------------------------------------------------------------
-- Reflection of the generated inner/outer classifier.
------------------------------------------------------------------------

data OuterCell : Grid.IntervalCell → Set where
  negativeOuterWitness : OuterCell Grid.negativeOuter
  positiveOuterWitness : OuterCell Grid.positiveOuter

record InnerCell (cell : Grid.IntervalCell) : Set where
  constructor innerCell
  field
    isInnerTrue : Grid.isInner cell ≡ true

open InnerCell public

data CellClassification (cell : Grid.IntervalCell) : Set where
  outer : OuterCell cell → CellClassification cell
  inner : InnerCell cell → CellClassification cell

classifyCell : (cell : Grid.IntervalCell) → CellClassification cell
classifyCell Grid.negativeOuter = outer negativeOuterWitness
classifyCell Grid.negativeInner = inner (innerCell refl)
classifyCell Grid.positiveInner = inner (innerCell refl)
classifyCell Grid.positiveOuter = outer positiveOuterWitness

data OuterCoordinate (cell : Grid.GridCell4) : Set where
  coordinate0 : OuterCell (Grid.c0 cell) → OuterCoordinate cell
  coordinate1 : OuterCell (Grid.c1 cell) → OuterCoordinate cell
  coordinate2 : OuterCell (Grid.c2 cell) → OuterCoordinate cell
  coordinate3 : OuterCell (Grid.c3 cell) → OuterCoordinate cell

allInnerFromInnerCoordinates :
  ∀ cell →
  InnerCell (Grid.c0 cell) →
  InnerCell (Grid.c1 cell) →
  InnerCell (Grid.c2 cell) →
  InnerCell (Grid.c3 cell) →
  Grid.allInner cell ≡ true
allInnerFromInnerCoordinates cell first second third fourth
  rewrite isInnerTrue first
        | isInnerTrue second
        | isInnerTrue third
        | isInnerTrue fourth = refl

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

regularCellHasOuterCoordinate :
  ∀ cell → Grid.allInner cell ≡ false → OuterCoordinate cell
regularCellHasOuterCoordinate cell regular
  with classifyCell (Grid.c0 cell)
... | outer first = coordinate0 first
... | inner first with classifyCell (Grid.c1 cell)
...   | outer second = coordinate1 second
...   | inner second with classifyCell (Grid.c2 cell)
...     | outer third = coordinate2 third
...     | inner third with classifyCell (Grid.c3 cell)
...       | outer fourth = coordinate3 fourth
...       | inner fourth =
  ⊥-elim
    (trueNotFalse
      (trans
        (sym (allInnerFromInnerCoordinates cell first second third fourth))
        regular))

------------------------------------------------------------------------
-- Literal point membership in one generated rational cell.
------------------------------------------------------------------------

record PointInGridCell (cell : Grid.GridCell4) : Set where
  constructor pointInGridCell
  field
    x0 x1 x2 x3 : ℚ
    x0Lower : Integral.lower (Grid.cellInterval (Grid.c0 cell)) ≤ x0
    x0Upper : x0 ≤ Integral.upper (Grid.cellInterval (Grid.c0 cell))
    x1Lower : Integral.lower (Grid.cellInterval (Grid.c1 cell)) ≤ x1
    x1Upper : x1 ≤ Integral.upper (Grid.cellInterval (Grid.c1 cell))
    x2Lower : Integral.lower (Grid.cellInterval (Grid.c2 cell)) ≤ x2
    x2Upper : x2 ≤ Integral.upper (Grid.cellInterval (Grid.c2 cell))
    x3Lower : Integral.lower (Grid.cellInterval (Grid.c3 cell)) ≤ x3
    x3Upper : x3 ≤ Integral.upper (Grid.cellInterval (Grid.c3 cell))

open PointInGridCell public

positiveOuterSquareLower : ∀ value → half ≤ value → quarter ≤ value * value
positiveOuterSquareLower value halfBelow =
  let
    valueNonnegative : 0ℚ ≤ value
    valueNonnegative = ℚP.≤-trans halfNonnegative halfBelow

    halfSquareBelowHalfValue : half * half ≤ half * value
    halfSquareBelowHalfValue =
      Interval.mulLeftNN half halfNonnegative halfBelow

    halfValueBelowSquare : half * value ≤ value * value
    halfValueBelowSquare =
      Interval.mulRightNN value valueNonnegative halfBelow
  in
  subst
    (λ lower → lower ≤ value * value)
    halfSquareQuarter
    (ℚP.≤-trans halfSquareBelowHalfValue halfValueBelowSquare)

negativeOuterSquareLower :
  ∀ value → value ≤ 0ℚ - half → quarter ≤ value * value
negativeOuterSquareLower value belowNegativeHalf =
  let
    reflectedBoundRaw : - (0ℚ - half) ≤ - value
    reflectedBoundRaw = ℚP.neg-mono-≤ belowNegativeHalf

    reflectedBound : half ≤ - value
    reflectedBound =
      subst
        (λ lower → lower ≤ - value)
        (ℚRing.solve-∀ half)
        reflectedBoundRaw

    reflectedSquare : quarter ≤ (- value) * (- value)
    reflectedSquare = positiveOuterSquareLower (- value) reflectedBound
  in
  subst
    (λ upper → quarter ≤ upper)
    (ℚRing.solve-∀ value)
    reflectedSquare

outerSelectedSquare : ∀ {cell} →
  PointInGridCell cell → OuterCoordinate cell → ℚ
outerSelectedSquare point (coordinate0 _) = x0 point * x0 point
outerSelectedSquare point (coordinate1 _) = x1 point * x1 point
outerSelectedSquare point (coordinate2 _) = x2 point * x2 point
outerSelectedSquare point (coordinate3 _) = x3 point * x3 point

outerCoordinateSquareLower :
  ∀ {cell} →
  (point : PointInGridCell cell) →
  (outerCoordinate : OuterCoordinate cell) →
  quarter ≤ outerSelectedSquare point outerCoordinate
outerCoordinateSquareLower point (coordinate0 negativeOuterWitness) =
  negativeOuterSquareLower (x0 point) (x0Upper point)
outerCoordinateSquareLower point (coordinate0 positiveOuterWitness) =
  positiveOuterSquareLower (x0 point) (x0Lower point)
outerCoordinateSquareLower point (coordinate1 negativeOuterWitness) =
  negativeOuterSquareLower (x1 point) (x1Upper point)
outerCoordinateSquareLower point (coordinate1 positiveOuterWitness) =
  positiveOuterSquareLower (x1 point) (x1Lower point)
outerCoordinateSquareLower point (coordinate2 negativeOuterWitness) =
  negativeOuterSquareLower (x2 point) (x2Upper point)
outerCoordinateSquareLower point (coordinate2 positiveOuterWitness) =
  positiveOuterSquareLower (x2 point) (x2Lower point)
outerCoordinateSquareLower point (coordinate3 negativeOuterWitness) =
  negativeOuterSquareLower (x3 point) (x3Upper point)
outerCoordinateSquareLower point (coordinate3 positiveOuterWitness) =
  positiveOuterSquareLower (x3 point) (x3Lower point)

------------------------------------------------------------------------
-- Four-dimensional square gap.  We keep this theorem independent of sine so
-- the later transcendental transfer has a clean, falsifiable input.
------------------------------------------------------------------------

normalizedMomentumSquare : ∀ {cell} → PointInGridCell cell → ℚ
normalizedMomentumSquare point =
  x0 point * x0 point
  + x1 point * x1 point
  + x2 point * x2 point
  + x3 point * x3 point

sumThreeSquaresNonnegative : ∀ first second third →
  0ℚ ≤ first * first + second * second + third * third
sumThreeSquaresNonnegative first second third =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (FiniteL2.squareNonnegative first)
      (FiniteL2.squareNonnegative second))
    (FiniteL2.squareNonnegative third)

selectedSquareBelowTotal :
  ∀ {cell} →
  (point : PointInGridCell cell) →
  (outerCoordinate : OuterCoordinate cell) →
  outerSelectedSquare point outerCoordinate ≤ normalizedMomentumSquare point
selectedSquareBelowTotal point (coordinate0 _) =
  let
    tailNN = sumThreeSquaresNonnegative (x1 point) (x2 point) (x3 point)
    raw :
      x0 point * x0 point
      ≤ x0 point * x0 point
        + (x1 point * x1 point + x2 point * x2 point + x3 point * x3 point)
    raw =
      subst
        (λ left → left ≤ x0 point * x0 point
          + (x1 point * x1 point + x2 point * x2 point + x3 point * x3 point))
        (sym (ℚP.+-identityʳ (x0 point * x0 point)))
        (ℚP.+-monoˡ-≤ (x0 point * x0 point) tailNN)
  in
  subst
    (λ upper → x0 point * x0 point ≤ upper)
    (ℚRing.solve-∀ (x0 point) (x1 point) (x2 point) (x3 point))
    raw
selectedSquareBelowTotal point (coordinate1 _) =
  let
    tailNN = sumThreeSquaresNonnegative (x0 point) (x2 point) (x3 point)
    raw :
      x1 point * x1 point
      ≤ x1 point * x1 point
        + (x0 point * x0 point + x2 point * x2 point + x3 point * x3 point)
    raw =
      subst
        (λ left → left ≤ x1 point * x1 point
          + (x0 point * x0 point + x2 point * x2 point + x3 point * x3 point))
        (sym (ℚP.+-identityʳ (x1 point * x1 point)))
        (ℚP.+-monoˡ-≤ (x1 point * x1 point) tailNN)
  in
  subst
    (λ upper → x1 point * x1 point ≤ upper)
    (ℚRing.solve-∀ (x0 point) (x1 point) (x2 point) (x3 point))
    raw
selectedSquareBelowTotal point (coordinate2 _) =
  let
    tailNN = sumThreeSquaresNonnegative (x0 point) (x1 point) (x3 point)
    raw :
      x2 point * x2 point
      ≤ x2 point * x2 point
        + (x0 point * x0 point + x1 point * x1 point + x3 point * x3 point)
    raw =
      subst
        (λ left → left ≤ x2 point * x2 point
          + (x0 point * x0 point + x1 point * x1 point + x3 point * x3 point))
        (sym (ℚP.+-identityʳ (x2 point * x2 point)))
        (ℚP.+-monoˡ-≤ (x2 point * x2 point) tailNN)
  in
  subst
    (λ upper → x2 point * x2 point ≤ upper)
    (ℚRing.solve-∀ (x0 point) (x1 point) (x2 point) (x3 point))
    raw
selectedSquareBelowTotal point (coordinate3 _) =
  let
    tailNN = sumThreeSquaresNonnegative (x0 point) (x1 point) (x2 point)
    raw :
      x3 point * x3 point
      ≤ x3 point * x3 point
        + (x0 point * x0 point + x1 point * x1 point + x2 point * x2 point)
    raw =
      subst
        (λ left → left ≤ x3 point * x3 point
          + (x0 point * x0 point + x1 point * x1 point + x2 point * x2 point))
        (sym (ℚP.+-identityʳ (x3 point * x3 point)))
        (ℚP.+-monoˡ-≤ (x3 point * x3 point) tailNN)
  in
  subst
    (λ upper → x3 point * x3 point ≤ upper)
    (ℚRing.solve-∀ (x0 point) (x1 point) (x2 point) (x3 point))
    raw

regularNormalizedMomentumSquareLower :
  ∀ cell →
  Grid.allInner cell ≡ false →
  (point : PointInGridCell cell) →
  quarter ≤ normalizedMomentumSquare point
regularNormalizedMomentumSquareLower cell regular point =
  let
    outerCoordinate = regularCellHasOuterCoordinate cell regular
  in
  ℚP.≤-trans
    (outerCoordinateSquareLower point outerCoordinate)
    (selectedSquareBelowTotal point outerCoordinate)

regularGridOuterCoordinateLevel : ProofLevel
regularGridOuterCoordinateLevel = machineChecked

regularGridNormalizedMomentumGapLevel : ProofLevel
regularGridNormalizedMomentumGapLevel = machineChecked
