module DASHI.Physics.YangMills.BalabanStrongCouplingSU4DHessianAssemblyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- SOURCE STRUCTURE
--
-- Lemma 4.1 separates the Wilson-action Hessian estimate into:
--
--   diagonal edge pairs:     2(d-1) N |beta| |v|^2,
--   distinct edge pairs:     6(d-1) N |beta| |v|^2.
--
-- In d=4 these are 6 and 18, and their sum is the published coefficient 24.
--
-- DASHI CONTRIBUTION
--
-- Prove the signed-order assembly over exact rationals.  This is not only the
-- coefficient identity: given actual diagonal and cross upper estimates and an
-- exact decomposition of the absolute Hessian budget, the combined 24 N|beta|
-- bound follows.  The remaining physical work is to instantiate the two input
-- bounds with the repository's literal quaternion derivative atoms.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

diagonalBudget : ℚ → ℚ → ℚ → ℚ
diagonalBudget rankN betaMagnitude tangentNormSq =
  (+ 6 / 1) * rankN * betaMagnitude * tangentNormSq

crossBudget : ℚ → ℚ → ℚ → ℚ
crossBudget rankN betaMagnitude tangentNormSq =
  (+ 18 / 1) * rankN * betaMagnitude * tangentNormSq

totalHessianBudget : ℚ → ℚ → ℚ → ℚ
totalHessianBudget rankN betaMagnitude tangentNormSq =
  (+ 24 / 1) * rankN * betaMagnitude * tangentNormSq

diagonalPlusCrossBudgetExact :
  ∀ rankN betaMagnitude tangentNormSq →
  diagonalBudget rankN betaMagnitude tangentNormSq
    + crossBudget rankN betaMagnitude tangentNormSq
  ≡ totalHessianBudget rankN betaMagnitude tangentNormSq
diagonalPlusCrossBudgetExact rankN betaMagnitude tangentNormSq =
  solve (rankN ∷ betaMagnitude ∷ tangentNormSq ∷ [])

assemblePublishedHessianUpper :
  ∀ rankN betaMagnitude tangentNormSq
    diagonalContribution crossContribution absoluteHessian →
  absoluteHessian ≡ diagonalContribution + crossContribution →
  diagonalContribution
    ≤ diagonalBudget rankN betaMagnitude tangentNormSq →
  crossContribution
    ≤ crossBudget rankN betaMagnitude tangentNormSq →
  absoluteHessian
    ≤ totalHessianBudget rankN betaMagnitude tangentNormSq
assemblePublishedHessianUpper
    rankN betaMagnitude tangentNormSq
    diagonalContribution crossContribution absoluteHessian
    decomposition diagonalUpper crossUpper =
  let
    summedUpper :
      diagonalContribution + crossContribution
      ≤ diagonalBudget rankN betaMagnitude tangentNormSq
        + crossBudget rankN betaMagnitude tangentNormSq
    summedUpper = ℚP.+-mono-≤ diagonalUpper crossUpper

    normalizedUpper :
      diagonalContribution + crossContribution
      ≤ totalHessianBudget rankN betaMagnitude tangentNormSq
    normalizedUpper =
      subst
        (λ selected → diagonalContribution + crossContribution ≤ selected)
        (diagonalPlusCrossBudgetExact
          rankN betaMagnitude tangentNormSq)
        summedUpper
  in
  subst
    (λ selected → selected
      ≤ totalHessianBudget rankN betaMagnitude tangentNormSq)
    (sym decomposition)
    normalizedUpper

configuredSU2InteriorTotalBudgetExact :
  totalHessianBudget (+ 2 / 1) (+ 1 / 96) (+ 1 / 1)
  ≡ + 1 / 2
configuredSU2InteriorTotalBudgetExact = solve []
