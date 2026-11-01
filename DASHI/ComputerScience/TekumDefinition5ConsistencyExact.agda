module DASHI.ComputerScience.TekumDefinition5ConsistencyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _≤_; _<_)
open import Data.Empty using (⊥)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; _-_)
import Data.Nat.Properties as NatP

import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional

------------------------------------------------------------------------
-- SOURCE AUDIT: Hunhold Definition 5 vs. its explanatory paragraph.
--
-- Equation (1) adjusts an overflowing integer sum by
--
--   (3^n + 1) / 2 = A_n + 1,
--
-- whereas the paragraph immediately below describes fixed-width addition as
-- discarding the carry.  Carry discard on n balanced trits is cyclic modulo
-- 3^n = 2*A_n+1.  Those operations are not identical.
--
-- We preserve both statements as separate source claims instead of silently
-- replacing Equation (1) by the carry-discard interpretation.
------------------------------------------------------------------------

sourceOverflowAdjustment : Nat → Nat
sourceOverflowAdjustment n = Positional.center n + 1

sourcePositiveOverflow : Nat → ℤ → ℤ
sourcePositiveOverflow n s = s ℤ.- (+ (sourceOverflowAdjustment n))

-- Width one: A_1 = 1 and the overflowing sum 1+1 = 2.
-- Printed Equation (1): 2 - (A_1+1) = 0.
definition5WidthOnePositiveOverflow :
  sourcePositiveOverflow 1 (+ 2) ≡ + 0
definition5WidthOnePositiveOverflow = refl

-- Literal carry discard in one balanced trit sends 1+1 to T = -1.
carryDiscardWidthOnePositiveOverflow : ℤ
carryDiscardWidthOnePositiveOverflow = -[1+ 0 ]

definition5DiffersFromCarryDiscardAtWidthOne :
  ¬ (sourcePositiveOverflow 1 (+ 2)
      ≡ carryDiscardWidthOnePositiveOverflow)
definition5DiffersFromCarryDiscardAtWidthOne ()

------------------------------------------------------------------------
-- The anchor does not exercise this discrepancy.
--
-- |t| has an integer magnitude m in [0,A_n], so |t|-A_n is never positive;
-- in particular it cannot enter Definition 5's positive-overflow branch.
------------------------------------------------------------------------

anchorSubtractionNeverNeedsPositiveOverflow :
  ∀ {n m} → m ≤ Positional.center n → ¬ (Positional.center n < m)
anchorSubtractionNeverNeedsPositiveOverflow m≤A = NatP.≤⇒≯ m≤A

record Definition5SourceBoundary : Set where
  constructor definition5SourceBoundary
  field
    printedEquationUsesHalfThreePowerPlusOne : Bool
    proseDescribesCarryDiscard : Bool
    equationAndCarryDiscardCoincideGenerally : Bool
    anchorDependsOnOverflowDiscrepancy : Bool

sourceEquationAndCarryDescriptionSeparated : Definition5SourceBoundary
sourceEquationAndCarryDescriptionSeparated =
  definition5SourceBoundary true true false false
