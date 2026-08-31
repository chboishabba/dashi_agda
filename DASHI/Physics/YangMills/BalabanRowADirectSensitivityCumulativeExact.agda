module DASHI.Physics.YangMills.BalabanRowADirectSensitivityCumulativeExact where

------------------------------------------------------------------------
-- ROW A: PER-SHELL O(g^6) DIRECT SENSITIVITY -> UNIFORM CUMULATIVE BUDGET
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as ℕ
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact as Cubic
import DASHI.Physics.YangMills.BalabanRowASixthSensitivityFromCubicTelescopeExact as Sixth

sumDirect : (Nat → ℚ) → Nat → ℚ
sumDirect s zero = 0ℚ
sumDirect s (suc n) = sumDirect s n + s n

record DirectSixthSensitivityData : Set₁ where
  field
    coupling directSensitivity : Nat → ℚ
    coefficient : ℚ

    coefficientNonnegative : 0ℚ ≤ coefficient
    directSensitivityNonnegative : ∀ j → 0ℚ ≤ directSensitivity j
    directSensitivitySixthBound : ∀ j →
      directSensitivity j ≤ coefficient * Sixth.sixth (coupling j)

open DirectSixthSensitivityData public

cumulativeDirectBelowSixth :
  (dataSet : DirectSixthSensitivityData) → ∀ K →
  sumDirect (directSensitivity dataSet) K
  ≤ coefficient dataSet * Sixth.sumSixth (coupling dataSet) K
cumulativeDirectBelowSixth dataSet zero =
  subst (λ right → 0ℚ ≤ right)
    (ℚRing.solve-∀ (coefficient dataSet)) ℚP.≤-refl
cumulativeDirectBelowSixth dataSet (suc n) =
  let
    induction = cumulativeDirectBelowSixth dataSet n
    current = directSensitivitySixthBound dataSet n
    added = ℚP.+-mono-≤ induction current
  in
  subst
    (λ upper → sumDirect (directSensitivity dataSet) (suc n) ≤ upper)
    (ℚRing.solve-∀
      (coefficient dataSet)
      (Sixth.sumSixth (coupling dataSet) n)
      (Sixth.sixth (coupling dataSet n)))
    added

sumSixthCong :
  ∀ {left right : Nat → ℚ} →
  (∀ j → left j ≡ right j) →
  ∀ K → Sixth.sumSixth left K ≡ Sixth.sumSixth right K
sumSixthCong same zero = refl
sumSixthCong same (suc n) =
  cong₂ _+_ (sumSixthCong same n)
    (cong Sixth.sixth (same n))

module FromFlow {cutoff : Nat}
    (flow : Cubic.InverseSquareMarginFlow cutoff)
    (dataSet : DirectSixthSensitivityData)
    (sameCoupling : ∀ j → coupling dataSet j ≡ Cubic.coupling flow j) where

  cumulativeDirectBudgetInTube :
    0ℚ ≤ Cubic.marginConstant flow →
    ∀ {gamma tubeWidth} →
    0ℚ ≤ gamma →
    (∀ j → 0ℚ ≤ Cubic.coupling flow j) →
    (∀ j → Cubic.coupling flow j ≤ gamma) →
    (∀ K → Cubic.coupling flow K - Cubic.coupling flow zero ≤ tubeWidth) →
    ∀ K → K ℕ.≤ cutoff →
    Cubic.marginConstant flow * sumDirect (directSensitivity dataSet) K
      ≤ (Cubic.twoℚ * coefficient dataSet * Sixth.cube gamma) * tubeWidth
  cumulativeDirectBudgetInTube marginNN {gamma} {tubeWidth}
      gammaNN couplingNN couplingBelow tube K K≤ =
    let
      directToSixth = cumulativeDirectBelowSixth dataSet K

      sixthSame = sumSixthCong sameCoupling K

      directToFlowSixth :
        sumDirect (directSensitivity dataSet) K
        ≤ coefficient dataSet * Sixth.sumSixth (Cubic.coupling flow) K
      directToFlowSixth =
        subst
          (λ right → sumDirect (directSensitivity dataSet) K
            ≤ coefficient dataSet * right)
          sixthSame directToSixth

      scaledDirect = Cubic.scaleˡ-nonNeg marginNN directToFlowSixth

      sixthBudget = Sixth.FromFlow.sixthSensitivityBudgetInTube flow
        marginNN gammaNN couplingNN couplingBelow tube K K≤

      scaledSixth = Norm.scaleNonnegative
        (coefficient dataSet)
        (coefficientNonnegative dataSet)
        sixthBudget
    in
    ℚP.≤-trans
      scaledDirect
      (subst
        (λ upper →
          Cubic.marginConstant flow
            * (coefficient dataSet * Sixth.sumSixth (Cubic.coupling flow) K)
          ≤ upper)
        (ℚRing.solve-∀
          (Cubic.marginConstant flow)
          (coefficient dataSet)
          (Sixth.sumSixth (Cubic.coupling flow) K)
          gamma tubeWidth)
        scaledSixth)

rowADirectSixthFiniteSumAlgebraLevel : ProofLevel
rowADirectSixthFiniteSumAlgebraLevel = machineChecked

rowADirectSixthTubeBudgetAlgebraLevel : ProofLevel
rowADirectSixthTubeBudgetAlgebraLevel = machineChecked

literalRowADirectSixthSensitivityInstantiationLevel : ProofLevel
literalRowADirectSixthSensitivityInstantiationLevel = conditional
