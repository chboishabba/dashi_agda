module DASHI.Physics.YangMills.BalabanP33PhysicalInfiniteDiscountedLossExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984),
-- 223--250. DOI: 10.1007/BF01240221.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban III. Convergence",
-- Annales Henri Poincare 15 (2014), 2133--2175.
-- DOI: 10.1007/s00023-013-0303-3.
--
-- DASHI CONTRIBUTION
--
-- For one-step losses bounded by E theta^j, the dyadic gap pullback pays
--
--   sum_{j=0}^{N-1} 2^{-(j+1)} E theta^j.
--
-- This module proves the exact finite, division-free formula
--
--   (2-theta) Loss_N = E (1-(theta/2)^N).
--
-- Hence the proposed infinite budget E/(2-theta) is not merely quoted: it is
-- the zero-tail endpoint of an exact recurrence.  Physical estimates producing
-- E and theta remain separate from this completed algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

half : ℚ
half = + 1 / 2

power : ℚ → Nat → ℚ
power ratio zero = 1ℚ
power ratio (suc exponent) = ratio * power ratio exponent

geometricPartialSum : ℚ → Nat → ℚ
geometricPartialSum ratio zero = 0ℚ
geometricPartialSum ratio (suc count) =
  geometricPartialSum ratio count + power ratio count

discountedGeometricLoss : ℚ → ℚ → Nat → ℚ
discountedGeometricLoss envelope theta count =
  half * envelope * geometricPartialSum (half * theta) count

geometricPartialSumClosedForm : ∀ ratio count →
  (1ℚ - ratio) * geometricPartialSum ratio count
  ≡ 1ℚ - power ratio count
geometricPartialSumClosedForm ratio zero =
  ℚRing.solve-∀ ratio
geometricPartialSumClosedForm ratio (suc count)
  rewrite geometricPartialSumClosedForm ratio count =
  ℚRing.solve-∀ ratio (power ratio count)

discountedGeometricLossClosedForm : ∀ envelope theta count →
  ((+ 2 / 1) - theta)
    * discountedGeometricLoss envelope theta count
  ≡ envelope * (1ℚ - power (half * theta) count)
discountedGeometricLossClosedForm envelope theta count =
  trans
    (ℚRing.solve-∀
      envelope theta
      (geometricPartialSum (half * theta) count))
    (cong (envelope *_)
      (geometricPartialSumClosedForm (half * theta) count))

record InfiniteDiscountedLossBudget
    (envelope theta budget : ℚ) : Set where
  field
    budgetEquation :
      ((+ 2 / 1) - theta) * budget ≡ envelope

open InfiniteDiscountedLossBudget public

discountedLossTailExact :
  ∀ envelope theta budget →
  InfiniteDiscountedLossBudget envelope theta budget →
  ∀ count →
  ((+ 2 / 1) - theta)
    * (budget - discountedGeometricLoss envelope theta count)
  ≡ envelope * power (half * theta) count
discountedLossTailExact envelope theta budget witness count =
  trans
    (ℚRing.solve-∀
      ((+ 2 / 1) - theta)
      budget
      (discountedGeometricLoss envelope theta count))
    (trans
      (cong₂ _-_
        (budgetEquation witness)
        (discountedGeometricLossClosedForm envelope theta count))
      (ℚRing.solve-∀ envelope (power (half * theta) count)))

record StrictPhysicalLossBudget
    (envelope theta initialPhysicalGap budget : ℚ) : Set where
  field
    infiniteBudget :
      InfiniteDiscountedLossBudget envelope theta budget
    strictBudgetBelowGap : Set
    strictBudgetBelowGapEvidence : strictBudgetBelowGap

open StrictPhysicalLossBudget public

discountedGeometricGapAlgebraLevel : ProofLevel
discountedGeometricGapAlgebraLevel = machineChecked

infiniteDiscountedLossFormulaLevel : ProofLevel
infiniteDiscountedLossFormulaLevel = machineChecked

physicalGeometricLossProducerLevel : ProofLevel
physicalGeometricLossProducerLevel = conditional
