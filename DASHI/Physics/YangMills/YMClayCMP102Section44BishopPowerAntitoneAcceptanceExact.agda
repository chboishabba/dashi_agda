module DASHI.Physics.YangMills.YMClayCMP102Section44BishopPowerAntitoneAcceptanceExact where

------------------------------------------------------------------------
-- Section44: all-index BISHOP real-order power comparison for
-- the actual signed CMP102 input modulus u=|X|<=1/4<=1.
-- This is analytic power order, NOT just finite Nat degrees.
-- Next source debt is original filtered positive Cauchy summation.
-- Agda 2.9 --safe/native acceptance UNRUN.
------------------------------------------------------------------------
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
import Real as R
import DASHI.Foundations.BishopUnitIntervalPowerSuccessorExact as Power

originalBishopPowerSuccessor :
  ∀ u → R.NonNegative u → R._≤_ u R.1ℝ →
  ∀ n → R._≤_ (R.pow u (Agda.Builtin.Nat.suc n)) (R.pow u n)
originalBishopPowerSuccessor = Power.bishopUnitIntervalPowerSuccessorAntitone

originalBishopPowerAllExponentOrders :
  ∀ u → R.NonNegative u → R._≤_ u R.1ℝ →
  ∀ {small large} → small ≤ large →
  R._≤_ (R.pow u large) (R.pow u small)
originalBishopPowerAllExponentOrders = Power.bishopUnitIntervalPowerAntitone
