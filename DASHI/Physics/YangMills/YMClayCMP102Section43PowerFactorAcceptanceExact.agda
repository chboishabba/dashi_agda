module DASHI.Physics.YangMills.YMClayCMP102Section43PowerFactorAcceptanceExact where
------------------------------------------------------------------------
-- Section43 native original A/B/c1 filtered exponent-factor source.
-- Actual scalar Bishop positive finite sum and mass remain a separate
-- source construction; physical Wilson/OS/same-H gap unrelated.
-- Agda 2.9 safe graph pending native elaboration.
------------------------------------------------------------------------
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _∸_)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import DASHI.Foundations.FiniteCauchyOriginalShiftedDegreeFilterExact as D

originalAActualPowerFactor :
  ∀ n i j → n ≤ i + j →
  suc (i + j) ≡ suc n + (suc (i + j) ∸ suc n)
originalAActualPowerFactor = D.originalAFilteredPowerFactor

originalBActualPowerFactor :
  ∀ n i j → n ≤ i + j →
  suc (suc (i + j)) ≡ suc (suc n) +
    (suc (suc (i + j)) ∸ suc (suc n))
originalBActualPowerFactor = D.originalBFilteredPowerFactor

originalBTrueFirstCountFactor :
  ∀ i j → suc (suc (i + j)) ≡ suc zero +
    (suc (suc (i + j)) ∸ suc zero)
originalBTrueFirstCountFactor = D.originalBCountOnePowerFactor
