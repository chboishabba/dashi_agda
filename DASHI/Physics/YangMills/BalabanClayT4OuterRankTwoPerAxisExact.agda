module DASHI.Physics.YangMills.BalabanClayT4OuterRankTwoPerAxisExact where

------------------------------------------------------------------------
-- EXACT FINITE RANK CONTRIBUTION: 2 PER OUTER AXIS.
--
-- For the actual generated 4^4 Brillouin grid, the unsigned
-- outer-coordinate rank is already computed by Geometry.outerCount.
-- This module verifies the algebraic rank tally:
--
--   sum_mu 2 * indicator(outer coordinate mu) == 2 * outerCount.
--
-- This is exactly the FINITE summation part of the proposed
-- q-hat-square >= 2m bound.
--
-- IMPORTANT: The analytic premise
--   |q_mu| >= pi/2 => 4 sin^2(q_mu/2) >= 2
-- must still be proved for the literal source q=pi*x and connected to
-- the actual hatMomentumSquared atom interval. This file does NOT
-- claim a physically certified denominator lower bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)

import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Geometry

twoPerOuterAxis : Grid.IntervalCell → Nat
twoPerOuterAxis Grid.negativeOuter = 2
twoPerOuterAxis Grid.negativeInner = 0
twoPerOuterAxis Grid.positiveInner = 0
twoPerOuterAxis Grid.positiveOuter = 2

twoPerOuterAxisIsTwiceWeight :
  ∀ axis →
  twoPerOuterAxis axis ≡ 2 * Geometry.outerWeight axis
twoPerOuterAxisIsTwiceWeight Grid.negativeOuter = refl
twoPerOuterAxisIsTwiceWeight Grid.negativeInner = refl
twoPerOuterAxisIsTwiceWeight Grid.positiveInner = refl
twoPerOuterAxisIsTwiceWeight Grid.positiveOuter = refl

fourAxisLowerRankContribution : Grid.GridCell4 → Nat
fourAxisLowerRankContribution cell =
  twoPerOuterAxis (Grid.c0 cell) +
  twoPerOuterAxis (Grid.c1 cell) +
  twoPerOuterAxis (Grid.c2 cell) +
  twoPerOuterAxis (Grid.c3 cell)

fourAxisLowerRankContributionIsTwiceRank :
  ∀ cell →
  fourAxisLowerRankContribution cell
    ≡ 2 * Geometry.outerCount cell
fourAxisLowerRankContributionIsTwiceRank cell
  rewrite twoPerOuterAxisIsTwiceWeight (Grid.c0 cell)
        | twoPerOuterAxisIsTwiceWeight (Grid.c1 cell)
        | twoPerOuterAxisIsTwiceWeight (Grid.c2 cell)
        | twoPerOuterAxisIsTwiceWeight (Grid.c3 cell) =
  solve 4
    (λ a b c d →
      (((con 2 :* a) :+ (con 2 :* b)) :+
        (con 2 :* c)) :+ (con 2 :* d)
      := con 2 :* (((a :+ b) :+ c) :+ d))
    refl
    (Geometry.outerWeight (Grid.c0 cell))
    (Geometry.outerWeight (Grid.c1 cell))
    (Geometry.outerWeight (Grid.c2 cell))
    (Geometry.outerWeight (Grid.c3 cell))
