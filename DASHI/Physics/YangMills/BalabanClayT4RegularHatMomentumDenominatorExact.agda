module DASHI.Physics.YangMills.BalabanClayT4RegularHatMomentumDenominatorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- On a regular Brillouin cell at least one normalized momentum coordinate is
-- outer.  For the Wilson propagator
--
--   hat{k}^2 = 4 sum_mu sin^2(k_mu/2),
--
-- strict positivity therefore needs only ONE lower bound on the sine-half
-- square of that outer coordinate.  This module proves the remaining rational
-- implication exactly.  Thus the analytic denominator leaf is reduced to the
-- scalar trigonometric statement on the two outer intervals; no four-variable
-- denominator estimate is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4RegularGridOuterAxisExact as Outer

four : ℚ
four = + 4 / 1

sumSquares : ℚ → ℚ → ℚ → ℚ → ℚ
sumSquares s0 s1 s2 s3 =
  FiniteL2.square s0 + FiniteL2.square s1
  + FiniteL2.square s2 + FiniteL2.square s3

hatMomentumSquaredFromSineHalf : ℚ → ℚ → ℚ → ℚ → ℚ
hatMomentumSquaredFromSineHalf s0 s1 s2 s3 =
  four * sumSquares s0 s1 s2 s3

selectedSine :
  ∀ {cell} → Outer.OuterAxisWitness cell →
  ℚ → ℚ → ℚ → ℚ → ℚ
selectedSine (Outer.outer0 _) s0 s1 s2 s3 = s0
selectedSine (Outer.outer1 _) s0 s1 s2 s3 = s1
selectedSine (Outer.outer2 _) s0 s1 s2 s3 = s2
selectedSine (Outer.outer3 _) s0 s1 s2 s3 = s3

leftBelowAddNonnegative :
  ∀ left right → 0ℚ ≤ right → left ≤ left + right
leftBelowAddNonnegative left right rightNN =
  subst
    (λ lower → lower ≤ left + right)
    (sym (ℚP.+-identityʳ left))
    (ℚP.+-monoˡ-≤ left rightNN)

selectedSquareBelowSumSquares :
  ∀ {cell} (witness : Outer.OuterAxisWitness cell) s0 s1 s2 s3 →
  FiniteL2.square (selectedSine witness s0 s1 s2 s3)
  ≤ sumSquares s0 s1 s2 s3
selectedSquareBelowSumSquares (Outer.outer0 _) s0 s1 s2 s3 =
  ℚP.≤-trans
    (leftBelowAddNonnegative
      (FiniteL2.square s0) (FiniteL2.square s1)
      (FiniteL2.squareNonnegative s1))
    (ℚP.≤-trans
      (leftBelowAddNonnegative
        (FiniteL2.square s0 + FiniteL2.square s1)
        (FiniteL2.square s2) (FiniteL2.squareNonnegative s2))
      (leftBelowAddNonnegative
        (FiniteL2.square s0 + FiniteL2.square s1 + FiniteL2.square s2)
        (FiniteL2.square s3) (FiniteL2.squareNonnegative s3)))
selectedSquareBelowSumSquares (Outer.outer1 _) s0 s1 s2 s3 =
  let
    first : FiniteL2.square s1 ≤ FiniteL2.square s0 + FiniteL2.square s1
    first = subst
      (λ right → FiniteL2.square s1 ≤ right)
      (ℚP.+-comm (FiniteL2.square s1) (FiniteL2.square s0))
      (leftBelowAddNonnegative
        (FiniteL2.square s1) (FiniteL2.square s0)
        (FiniteL2.squareNonnegative s0))
  in
  ℚP.≤-trans first
    (ℚP.≤-trans
      (leftBelowAddNonnegative
        (FiniteL2.square s0 + FiniteL2.square s1)
        (FiniteL2.square s2) (FiniteL2.squareNonnegative s2))
      (leftBelowAddNonnegative
        (FiniteL2.square s0 + FiniteL2.square s1 + FiniteL2.square s2)
        (FiniteL2.square s3) (FiniteL2.squareNonnegative s3)))
selectedSquareBelowSumSquares (Outer.outer2 _) s0 s1 s2 s3 =
  let
    prefixNN : 0ℚ ≤ FiniteL2.square s0 + FiniteL2.square s1
    prefixNN = FiniteL2.addNonnegative
      (FiniteL2.squareNonnegative s0) (FiniteL2.squareNonnegative s1)
    first : FiniteL2.square s2
      ≤ (FiniteL2.square s0 + FiniteL2.square s1) + FiniteL2.square s2
    first = subst
      (λ right → FiniteL2.square s2 ≤ right)
      (ℚP.+-comm (FiniteL2.square s2)
        (FiniteL2.square s0 + FiniteL2.square s1))
      (leftBelowAddNonnegative (FiniteL2.square s2)
        (FiniteL2.square s0 + FiniteL2.square s1) prefixNN)
  in
  ℚP.≤-trans first
    (leftBelowAddNonnegative
      (FiniteL2.square s0 + FiniteL2.square s1 + FiniteL2.square s2)
      (FiniteL2.square s3) (FiniteL2.squareNonnegative s3))
selectedSquareBelowSumSquares (Outer.outer3 _) s0 s1 s2 s3 =
  let
    prefixNN :
      0ℚ ≤ FiniteL2.square s0 + FiniteL2.square s1 + FiniteL2.square s2
    prefixNN = FiniteL2.addNonnegative
      (FiniteL2.addNonnegative
        (FiniteL2.squareNonnegative s0) (FiniteL2.squareNonnegative s1))
      (FiniteL2.squareNonnegative s2)
  in
  subst
    (λ right → FiniteL2.square s3 ≤ right)
    (ℚP.+-comm (FiniteL2.square s3)
      (FiniteL2.square s0 + FiniteL2.square s1 + FiniteL2.square s2))
    (leftBelowAddNonnegative (FiniteL2.square s3)
      (FiniteL2.square s0 + FiniteL2.square s1 + FiniteL2.square s2)
      prefixNN)

record RegularOuterSineSquareFloor
    (cell : Grid.GridCell4)
    (s0 s1 s2 s3 : ℚ) : Set where
  field
    regular : Grid.allInner cell ≡ false
    outerAxis : Outer.OuterAxisWitness cell
    floorSquared : ℚ
    floorSquaredPositive : 0ℚ < floorSquared
    floorBelowSelectedSquare :
      floorSquared
      ≤ FiniteL2.square (selectedSine outerAxis s0 s1 s2 s3)

open RegularOuterSineSquareFloor public

floorBelowHatMomentumSum :
  ∀ {cell s0 s1 s2 s3} →
  (data : RegularOuterSineSquareFloor cell s0 s1 s2 s3) →
  floorSquared data ≤ sumSquares s0 s1 s2 s3
floorBelowHatMomentumSum data =
  ℚP.≤-trans
    (floorBelowSelectedSquare data)
    (selectedSquareBelowSumSquares
      (outerAxis data) _ _ _ _)

regularDenominatorScalarFloorLevel : ProofLevel
regularDenominatorScalarFloorLevel = machineChecked

outerAxisSineHalfAnalyticInputLevel : ProofLevel
outerAxisSineHalfAnalyticInputLevel = conditional
