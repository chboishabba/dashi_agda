{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA2DirectHistoryShellSumRound108Exact where

------------------------------------------------------------------------
-- ROUND108 A2 BIDI WELD
--
-- Round103's literal CMP109 consumer wants one shell sequence q_j.  Existing
-- analysis already owns two logically distinct pieces:
--
--   * direct/current-coupling sensitivity, summed by the inverse-square cubic
--     telescope;
--   * irrelevant/polymer history sensitivity, summed geometrically.
--
-- Their pointwise sum is the exact q_j sequence consumed by the literal
-- same-history theorem.  The existing augmented gate makes every physical
-- finite partial sum strictly subunit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as ℕ
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanYM4RowAAugmentedShootingGateExact as Aug

sum : (Nat → ℚ) → Nat → ℚ
sum f zero = 0ℚ
sum f (suc n) = sum f n + f n

sumAgreeDirect :
  (f : Nat → ℚ) → ∀ K → sum f K ≡ Direct.sum₀ f K
sumAgreeDirect f zero = refl
sumAgreeDirect f (suc n) = cong (_+ f n) (sumAgreeDirect f n)

sumPointwiseAdd :
  (f h : Nat → ℚ) → ∀ K →
  sum (λ j → f j + h j) K ≡ sum f K + sum h K
sumPointwiseAdd f h zero = ℚRing.solve-∀
sumPointwiseAdd f h (suc n) =
  trans
    (cong (_+ (f n + h n)) (sumPointwiseAdd f h n))
    (ℚRing.solve-∀ (sum f n) (sum h n) (f n) (h n))

record DirectHistoryShellBudget (cutoff : Nat) : Set₁ where
  field
    augmented : Aug.AugmentedShootingSensitivityData cutoff
    historyShell : Nat → ℚ
    historyShellNonnegative : ∀ j → 0ℚ ≤ historyShell j
    historyPartialSumBound : ∀ K → K ℕ.≤ cutoff →
      sum historyShell K ≤ Aug.historyConstant augmented

open DirectHistoryShellBudget public

module Budget {cutoff : Nat} (dataSet : DirectHistoryShellBudget cutoff) where
  augmentedData = augmented dataSet
  directData = Aug.direct augmentedData
  module A = Aug.Augmented augmentedData

  totalShell : Nat → ℚ
  totalShell j = Direct.sensitivity directData j + historyShell dataSet j

  totalSumIdentity : ∀ K →
    sum totalShell K
    ≡ Direct.sum₀ (Direct.sensitivity directData) K
        + sum (historyShell dataSet) K
  totalSumIdentity K =
    trans
      (sumPointwiseAdd (Direct.sensitivity directData) (historyShell dataSet) K)
      (cong (λ x → x + sum (historyShell dataSet) K)
        (sumAgreeDirect (Direct.sensitivity directData) K))

  totalPartialSumBelowAugmentedQ :
    ∀ K → K ℕ.≤ cutoff →
    sum totalShell K ≤ A.qTotal K
  totalPartialSumBelowAugmentedQ K K≤ =
    let
      historyBound = historyPartialSumBound dataSet K K≤
      directRefl :
        Direct.sum₀ (Direct.sensitivity directData) K
        ≤ Direct.sum₀ (Direct.sensitivity directData) K
      directRefl = ℚP.≤-refl
      added = ℚP.+-mono-≤ directRefl historyBound
    in
    subst
      (λ left → left ≤ A.qTotal K)
      (totalSumIdentity K)
      added

  totalPartialSumBelowOne :
    ∀ K → K ℕ.≤ cutoff → sum totalShell K < 1ℚ
  totalPartialSumBelowOne K K≤ =
    ℚP.≤-<-trans
      (totalPartialSumBelowAugmentedQ K K≤)
      (A.qTotalBelowOne K K≤)

round108A2DirectHistoryShellSumLevel : ProofLevel
round108A2DirectHistoryShellSumLevel = machineChecked

literalCMP109DirectHistoryShellLipschitzRound108Level : ProofLevel
literalCMP109DirectHistoryShellLipschitzRound108Level = conditional
