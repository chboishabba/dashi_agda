module DASHI.Foundations.CoarseFineRefinementRegression where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.CoarseFineBranchAccessibilityExact as Branch
import DASHI.Foundations.DecimalNonaryRefinementBridgeExact as Refinement

------------------------------------------------------------------------
-- Focused regression surface: importing this module forces the generic branch
-- owner, decimal/nonary bridge, stage atlas reuse, recursive-fibre bridge and
-- J coarse/fine bridge to elaborate together.
------------------------------------------------------------------------

regression-five-first-refinement :
  Refinement.scaledNumerator
    (Refinement.canonicalDecimalRefinement Refinement.d5 1)
  ≡ 55
regression-five-first-refinement =
  Refinement.fiveFirstRefinementIs55Tenths

regression-nine-carry-target :
  Refinement.nextBandScaledNumerator Refinement.d9
  ≡ Refinement.refinementTargetNumerator Refinement.d9
regression-nine-carry-target =
  Refinement.nineTargetCarriesExactly

regression-ternary-subcritical :
  Branch.branchingRegime 3 (Branch.availability 5 18)
  ≡ Branch.subcritical
regression-ternary-subcritical =
  Branch.fiveEighteenthsTernarySubcritical

regression-jfine-numerator :
  Branch.jointExpectedNumerator 3 3 (Branch.availability 9 10)
  ≡ 19683
regression-jfine-numerator =
  Branch.threeAxisNinetyPercentNumerator

regression-twenty-seven : Nat
regression-twenty-seven = Branch.pow 3 3
