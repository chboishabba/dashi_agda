module DASHI.Foundations.BishopGeometricSeriesConvergenceExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE GEOMETRIC-SERIES CONVERGENCE ON 0 <= q < 1
--
-- This is the infinite-series companion to the existing finite geometric
-- bound.  The proof is a direct specialization of the vendored Bishop ratio
-- test (Sequence.proposition-3-6-1):
--
--   a_n = q^n,
--   |a_n| = a_n                    because q^n >= 0,
--   a_(n+1) = a_n q = q a_n.
--
-- Hence the ratio-test contraction is q itself.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (z≤n)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Geometric
open import DASHI.Physics.YangMills.CompactLieProofLevel

geometricTerm : BishopReal.ℝ → Nat → BishopReal.ℝ
geometricTerm q n = BishopReal.pow q n

geometricTermNonnegative :
  ∀ {q} →
  Geometric.BishopUnitIntervalRatio q →
  (n : Nat) →
  BishopReal.NonNegative (geometricTerm q n)
geometricTermNonnegative inputs n =
  Geometric.ratioPowerNonnegative inputs n

geometricAbsIsTerm :
  ∀ {q} →
  Geometric.BishopUnitIntervalRatio q →
  (n : Nat) →
  BishopReal._≃_
    (BishopReal.∣_∣ (geometricTerm q n))
    (geometricTerm q n)
geometricAbsIsTerm inputs n =
  BishopP.nonNegx⇒∣x∣≃x
    (geometricTermNonnegative inputs n)

geometricSuccessorAsRatioTimesPrevious :
  ∀ q n →
  BishopReal._≃_
    (geometricTerm q (suc n))
    (BishopReal._*_ q (geometricTerm q n))
geometricSuccessorAsRatioTimesPrevious q n =
  BishopP.≃-trans
    BishopP.≃-refl
    (BishopP.*-comm (geometricTerm q n) q)

geometricSuccessorContractive :
  ∀ {q} →
  (inputs : Geometric.BishopUnitIntervalRatio q) →
  (n : Nat) →
  BishopReal._≤_
    (BishopReal.∣_∣ (geometricTerm q (suc n)))
    (BishopReal._*_
      q
      (BishopReal.∣_∣ (geometricTerm q n)))
geometricSuccessorContractive {q} inputs n =
  BishopP.≤-respˡ-≃
    (BishopP.≃-trans
      (geometricAbsIsTerm inputs (suc n))
      (geometricSuccessorAsRatioTimesPrevious q n))
    (BishopP.≤-respʳ-≃
      (BishopP.*-congˡ q
        (BishopP.≃-symm
          (geometricAbsIsTerm inputs n)))
      BishopP.≤-refl)

geometricSeriesConvergent :
  ∀ {q} →
  Geometric.BishopUnitIntervalRatio q →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf (geometricTerm q))
geometricSeriesConvergent {q} inputs =
  BishopSequence.proposition-3-6-1
    (Geometric.ratioNonnegative inputs ,
      Geometric.ratioBelowOne inputs)
    (zero ,
      λ n _ →
        geometricSuccessorContractive inputs n)

bishopGeometricSeriesConvergenceLevel : ProofLevel
bishopGeometricSeriesConvergenceLevel = machineChecked
