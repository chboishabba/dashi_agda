module DASHI.Physics.YangMills.BalabanP33FiniteWeightedRowSumContractionExact where

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
-- Prove the finite weighted Schur/row-sum estimate needed by the physical
-- Neumann remainder.  For a literal finite kernel K and positive weight w,
--
--   |f(y)| <= M w(y),
--   sum_y |K(x,y)| w(y) <= rho w(x)
--
-- imply
--
--   |sum_y K(x,y) f(y)| <= rho M w(x).
--
-- The proof is a finite-list induction using the rational triangle inequality,
-- exact absolute-value multiplicativity and nonnegative multiplication.  Thus
-- the weighted residual contraction is reduced to concrete row sums of the
-- local parametrix kernel rather than accepted as a global operator premise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

sumKernel :
  ∀ {Site : Set} →
  List Site → (Site → ℚ) → ℚ
sumKernel [] value = 0ℚ
sumKernel (site ∷ sites) value = value site + sumKernel sites value

kernelApply :
  ∀ {Site : Set} →
  List Site → (Site → Site → ℚ) → (Site → ℚ) → Site → ℚ
kernelApply sites kernel vector left =
  sumKernel sites (λ right → kernel left right * vector right)

weightedRowSum :
  ∀ {Site : Set} →
  List Site → (Site → Site → ℚ) → (Site → ℚ) → Site → ℚ
weightedRowSum sites kernel weight left =
  sumKernel sites (λ right → ∣ kernel left right ∣ * weight right)

scaleDistributesOverAdd : ∀ scale left right →
  scale * (left + right) ≡ scale * left + scale * right
scaleDistributesOverAdd = ℚRing.solve-∀

reassociateWeightedProduct : ∀ kernelAbs majorant weightValue →
  kernelAbs * (majorant * weightValue)
  ≡ majorant * (kernelAbs * weightValue)
reassociateWeightedProduct = ℚRing.solve-∀

majorantRowScale : ∀ majorant contraction weightValue →
  majorant * (contraction * weightValue)
  ≡ contraction * majorant * weightValue
majorantRowScale = ℚRing.solve-∀

sumKernelScale :
  ∀ {Site : Set} (sites : List Site)
    (scale : ℚ) (value : Site → ℚ) →
  sumKernel sites (λ site → scale * value site)
  ≡ scale * sumKernel sites value
sumKernelScale [] scale value = ℚRing.solve []
sumKernelScale (site ∷ sites) scale value
  rewrite sumKernelScale sites scale value =
  ℚRing.solve-∀

absoluteKernelTermBound :
  ∀ kernelValue vectorValue majorant weightValue →
  0ℚ ≤ majorant →
  0ℚ ≤ weightValue →
  ∣ vectorValue ∣ ≤ majorant * weightValue →
  ∣ kernelValue * vectorValue ∣
  ≤ majorant * (∣ kernelValue ∣ * weightValue)
absoluteKernelTermBound
    kernelValue vectorValue majorant weightValue
    majorantNonnegative weightNonnegative vectorBound =
  let
    instance
      kernelAbsNN : NonNegative ∣ kernelValue ∣
      kernelAbsNN = ℚP.∣-∣-nonNeg kernelValue

      majorantNN : NonNegative majorant
      majorantNN = ℚ.nonNegative majorantNonnegative
  in
  subst
    (λ upper → ∣ kernelValue * vectorValue ∣ ≤ upper)
    (reassociateWeightedProduct ∣ kernelValue ∣ majorant weightValue)
    (subst
      (λ lower → lower ≤ ∣ kernelValue ∣ * (majorant * weightValue))
      (ℚP.∣p*q∣≡∣p∣*∣q∣ kernelValue vectorValue)
      (ℚP.*-monoˡ-≤-nonNeg ∣ kernelValue ∣ vectorBound))

absoluteKernelSumBound :
  ∀ {Site : Set}
    (sites : List Site)
    (kernel : Site → Site → ℚ)
    (vector weight : Site → ℚ)
    (majorant : ℚ) →
  0ℚ ≤ majorant →
  (∀ site → 0ℚ ≤ weight site) →
  (∀ site → ∣ vector site ∣ ≤ majorant * weight site) →
  ∀ left →
  ∣ kernelApply sites kernel vector left ∣
  ≤ majorant * weightedRowSum sites kernel weight left
absoluteKernelSumBound [] kernel vector weight majorant
    majorantNonnegative weightNonnegative vectorBound left =
  ℚP.≤-refl
absoluteKernelSumBound (right ∷ rights) kernel vector weight majorant
    majorantNonnegative weightNonnegative vectorBound left =
  ℚP.≤-trans
    (ℚP.∣p+q∣≤∣p∣+∣q∣
      (kernel left right * vector right)
      (kernelApply rights kernel vector left))
    (ℚP.≤-trans
      (ℚP.+-mono-≤
        (absoluteKernelTermBound
          (kernel left right) (vector right)
          majorant (weight right)
          majorantNonnegative (weightNonnegative right)
          (vectorBound right))
        (absoluteKernelSumBound
          rights kernel vector weight majorant
          majorantNonnegative weightNonnegative vectorBound left))
      (subst
        (λ upper →
          majorant * (∣ kernel left right ∣ * weight right)
          + majorant * weightedRowSum rights kernel weight left
          ≤ upper)
        (sym
          (scaleDistributesOverAdd majorant
            (∣ kernel left right ∣ * weight right)
            (weightedRowSum rights kernel weight left)))
        ℚP.≤-refl))

record FiniteWeightedRowContraction
    (Site : Set) : Set₁ where
  field
    sites : List Site
    kernel : Site → Site → ℚ
    weight : Site → ℚ
    contractionFactor : ℚ

    weightNonnegative : ∀ site → 0ℚ ≤ weight site
    contractionNonnegative : 0ℚ ≤ contractionFactor

    rowBound : ∀ left →
      weightedRowSum sites kernel weight left
      ≤ contractionFactor * weight left

open FiniteWeightedRowContraction public

weightedKernelContraction :
  ∀ {Site}
    (dataSet : FiniteWeightedRowContraction Site)
    (vector : Site → ℚ)
    (majorant : ℚ) →
  0ℚ ≤ majorant →
  (∀ site → ∣ vector site ∣ ≤ majorant * weight dataSet site) →
  ∀ left →
  ∣ kernelApply (sites dataSet) (kernel dataSet) vector left ∣
  ≤ contractionFactor dataSet * majorant * weight dataSet left
weightedKernelContraction dataSet vector majorant
    majorantNonnegative vectorBound left =
  let
    instance
      majorantNN : NonNegative majorant
      majorantNN = ℚ.nonNegative majorantNonnegative
  in
  ℚP.≤-trans
    (absoluteKernelSumBound
      (sites dataSet) (kernel dataSet) vector (weight dataSet)
      majorant majorantNonnegative
      (weightNonnegative dataSet) vectorBound left)
    (subst
      (λ upper →
        majorant * weightedRowSum
          (sites dataSet) (kernel dataSet) (weight dataSet) left
        ≤ upper)
      (majorantRowScale
        majorant (contractionFactor dataSet) (weight dataSet left))
      (ℚP.*-monoˡ-≤-nonNeg majorant
        (rowBound dataSet left)))

finiteWeightedRowSumInductionLevel : ProofLevel
finiteWeightedRowSumInductionLevel = machineChecked

finiteWeightedKernelContractionLevel : ProofLevel
finiteWeightedKernelContractionLevel = machineChecked

physicalResidualRowSumCriterionLevel : ProofLevel
physicalResidualRowSumCriterionLevel = machineChecked
