module DASHI.Physics.YangMills.BalabanClayT4RegularBoxDenominatorReductionExact where

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
-- Turn regular-box denominator positivity into a scalar outer-coordinate
-- trigonometric problem.  The 240-cell geometry supplies an outer axis.  A
-- caller supplies the actual sine-half values and ONE common positive square
-- floor on every outer coordinate.  The previous module then gives a uniform
-- lower bound for the complete four-dimensional hat-momentum sum.
--
-- Thus the next analytic target is no longer "prove every denominator on every
-- box positive".  It is the two one-dimensional inequalities on normalized
-- outer intervals:
--
--   q in [ 1/2, 1]  => sin^2(pi q/2) >= sigma_*,
--   q in [-1,-1/2]  => sin^2(pi q/2) >= sigma_*,
--
-- for one explicit rational sigma_* > 0.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4RegularGridOuterAxisExact as Outer
import DASHI.Physics.YangMills.BalabanClayT4RegularHatMomentumDenominatorExact as Denominator

record OuterSineSquareFloorFamily
    (cell : Grid.GridCell4)
    (s0 s1 s2 s3 : ℚ) : Set where
  field
    floorSquared : ℚ
    floorSquaredPositive : 0ℚ < floorSquared

    axis0OuterFloor : Grid.isInner (Grid.c0 cell) ≡ false →
      floorSquared ≤ FiniteL2.square s0
    axis1OuterFloor : Grid.isInner (Grid.c1 cell) ≡ false →
      floorSquared ≤ FiniteL2.square s1
    axis2OuterFloor : Grid.isInner (Grid.c2 cell) ≡ false →
      floorSquared ≤ FiniteL2.square s2
    axis3OuterFloor : Grid.isInner (Grid.c3 cell) ≡ false →
      floorSquared ≤ FiniteL2.square s3

open OuterSineSquareFloorFamily public

selectedOuterFloor :
  ∀ {cell s0 s1 s2 s3}
    (family : OuterSineSquareFloorFamily cell s0 s1 s2 s3)
    (witness : Outer.OuterAxisWitness cell) →
  floorSquared family
  ≤ FiniteL2.square (Denominator.selectedSine witness s0 s1 s2 s3)
selectedOuterFloor family (Outer.outer0 outer) = axis0OuterFloor family outer
selectedOuterFloor family (Outer.outer1 outer) = axis1OuterFloor family outer
selectedOuterFloor family (Outer.outer2 outer) = axis2OuterFloor family outer
selectedOuterFloor family (Outer.outer3 outer) = axis3OuterFloor family outer

regularBoxSineFloor :
  ∀ {cell s0 s1 s2 s3} →
  (family : OuterSineSquareFloorFamily cell s0 s1 s2 s3) →
  (regular : Grid.allInner cell ≡ false) →
  Denominator.RegularOuterSineSquareFloor cell s0 s1 s2 s3
regularBoxSineFloor {cell} family regular =
  let witness = Outer.regularCellHasOuterAxis cell regular
  in record
    { Denominator.RegularOuterSineSquareFloor.regular = regular
    ; Denominator.RegularOuterSineSquareFloor.outerAxis = witness
    ; Denominator.RegularOuterSineSquareFloor.floorSquared = floorSquared family
    ; Denominator.RegularOuterSineSquareFloor.floorSquaredPositive =
        floorSquaredPositive family
    ; Denominator.RegularOuterSineSquareFloor.floorBelowSelectedSquare =
        selectedOuterFloor family witness
    }

regularBoxUniformHatMomentumFloor :
  ∀ {cell s0 s1 s2 s3} →
  (family : OuterSineSquareFloorFamily cell s0 s1 s2 s3) →
  (regular : Grid.allInner cell ≡ false) →
  floorSquared family ≤ Denominator.sumSquares s0 s1 s2 s3
regularBoxUniformHatMomentumFloor family regular =
  Denominator.floorBelowHatMomentumSum (regularBoxSineFloor family regular)

regularBoxDenominatorReductionLevel : ProofLevel
regularBoxDenominatorReductionLevel = machineChecked

outerNormalizedSineSquareFloorLevel : ProofLevel
outerNormalizedSineSquareFloorLevel = conditional
