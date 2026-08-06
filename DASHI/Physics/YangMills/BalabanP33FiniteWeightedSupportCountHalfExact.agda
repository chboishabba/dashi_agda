module DASHI.Physics.YangMills.BalabanP33FiniteWeightedSupportCountHalfExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics, 1995 reprint.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Replace an opaque weighted residual row estimate by its literal finite
-- support-count calculation.  If every weighted residual entry is bounded by
--
--   epsilon * inflation * w(x)
--
-- and the enumerated support has N entries, then finite induction proves
--
--   sum_y |R(x,y)| w(y)
--     <= N * epsilon * inflation * w(x).
--
-- Thus the scalar inequality
--
--   N * epsilon * inflation <= 1/2
--
-- constructs the existing weighted-row contraction with factor 1/2.  For a
-- geometric weight, `inflation` is the literal rational value s^r coming from
-- the residual support radius.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedRowSumContractionExact as Row

oneHalf : ℚ
oneHalf = + 1 / 2

zeroRepeatedBudget : ∀ budget → 0ℚ ≡ 0ℚ * budget
zeroRepeatedBudget = ℚRing.solve-∀

repeatedBudgetStep :
  ∀ {A : Set} (value : A) values budget →
  budget + Sums.natAsRational (length values) * budget
  ≡ Sums.natAsRational (length (value ∷ values)) * budget
repeatedBudgetStep value values budget = ℚRing.solve-∀

finiteUniformSumBound :
  ∀ {A : Set}
    (values : List A) (term : A → ℚ) budget →
  (∀ value → term value ≤ budget) →
  Row.sumKernel values term
  ≤ Sums.natAsRational (length values) * budget
finiteUniformSumBound [] term budget pointwise =
  subst
    (λ upper → 0ℚ ≤ upper)
    (zeroRepeatedBudget budget)
    ℚP.≤-refl
finiteUniformSumBound (value ∷ values) term budget pointwise =
  ℚP.≤-trans
    (ℚP.+-mono-≤
      (pointwise value)
      (finiteUniformSumBound values term budget pointwise))
    (subst
      (λ upper →
        budget + Sums.natAsRational (length values) * budget ≤ upper)
      (repeatedBudgetStep value values budget)
      ℚP.≤-refl)

record FiniteWeightedSupportCountHalf
    (Site : Set) : Set₁ where
  field
    sites : List Site
    kernel : Site → Site → ℚ
    weight : Site → ℚ

    epsilon weightInflation : ℚ

    weightNonnegative : ∀ site → 0ℚ ≤ weight site

    entryWeightedBound : ∀ left right →
      ℚ.∣ kernel left right ∣ * weight right
      ≤ (epsilon * weightInflation) * weight left

    supportCountBudget : ∀ left →
      Sums.natAsRational (length sites)
        * ((epsilon * weightInflation) * weight left)
      ≤ oneHalf * weight left

open FiniteWeightedSupportCountHalf public

weightedRowBelowHalf :
  ∀ {Site}
    (dataSet : FiniteWeightedSupportCountHalf Site)
    left →
  Row.weightedRowSum
    (sites dataSet) (kernel dataSet) (weight dataSet) left
  ≤ oneHalf * weight dataSet left
weightedRowBelowHalf dataSet left =
  ℚP.≤-trans
    (finiteUniformSumBound
      (sites dataSet)
      (λ right →
        ℚ.∣ kernel dataSet left right ∣ * weight dataSet right)
      ((epsilon dataSet * weightInflation dataSet)
        * weight dataSet left)
      (entryWeightedBound dataSet left))
    (supportCountBudget dataSet left)

oneHalfNonnegative : 0ℚ ≤ oneHalf
oneHalfNonnegative = ℚP.nonNegative⁻¹ oneHalf

asHalfWeightedRowContraction :
  ∀ {Site} →
  FiniteWeightedSupportCountHalf Site →
  Row.FiniteWeightedRowContraction Site
asHalfWeightedRowContraction dataSet = record
  { Row.FiniteWeightedRowContraction.sites = sites dataSet
  ; Row.FiniteWeightedRowContraction.kernel = kernel dataSet
  ; Row.FiniteWeightedRowContraction.weight = weight dataSet
  ; Row.FiniteWeightedRowContraction.contractionFactor = oneHalf
  ; Row.FiniteWeightedRowContraction.weightNonnegative =
      weightNonnegative dataSet
  ; Row.FiniteWeightedRowContraction.contractionNonnegative =
      oneHalfNonnegative
  ; Row.FiniteWeightedRowContraction.rowBound =
      weightedRowBelowHalf dataSet
  }

weightedSupportCountInductionLevel : ProofLevel
weightedSupportCountInductionLevel = machineChecked

weightedSupportCountHalfContractionLevel : ProofLevel
weightedSupportCountHalfContractionLevel = machineChecked
