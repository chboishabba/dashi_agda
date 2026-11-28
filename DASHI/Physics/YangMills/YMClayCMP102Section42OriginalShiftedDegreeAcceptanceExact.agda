module DASHI.Physics.YangMills.YMClayCMP102Section42OriginalShiftedDegreeAcceptanceExact where

------------------------------------------------------------------------
-- Section42 original source A(c-1), B(c-2) Fin degree extraction.
-- Consumes a SINGLE actual Nat/Fin degree constructor; no
-- synthetic analytic series. Pending Bishop filtered-positive
-- rectangle order and Agda 2.9 --safe elaboration.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_)
import DASHI.Foundations.FiniteCauchyOriginalShiftedDegreeFilterExact as Degree

originalAOneExtraPower :
  ∀ n i j → n ≤ (i + j) → suc n ≤ suc (i + j)
originalAOneExtraPower = Degree.aOriginalShiftedCellDegree

originalBTwoExtraPowers :
  ∀ n i j → n ≤ (i + j) →
  suc (suc n) ≤ suc (suc (i + j))
originalBTwoExtraPowers = Degree.bOriginalShiftedCellDegree

originalBFirstCountPower :
  ∀ i j → suc zero ≤ suc (suc (i + j))
originalBFirstCountPower = Degree.bOriginalCountOneDegree
