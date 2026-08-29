module DASHI.Physics.YangMills.BalabanRowADirectQFromTubeExact where

------------------------------------------------------------------------
-- ROW A: SIXTH-ORDER TUBE BUDGET -> EXPLICIT DIRECT LIPSCHITZ CONSTANT
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanRowASixthSensitivityFromCubicTelescopeExact as Sixth
import DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact as Cubic

mulNN : ∀ {left right} → 0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
mulNN {left} {right} leftNN rightNN =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = ℚ.nonNegative leftNN
      rightNonnegative : NonNegative right
      rightNonnegative = ℚ.nonNegative rightNN
  in
  ℚP.nonNegative⁻¹ (left * right)

record DirectTubeToInputSensitivity : Set₁ where
  field
    cumulativeDirect inputDistance tubeWidth : ℚ
    margin marginInverse : ℚ
    coefficient gamma tubeResponse : ℚ

    marginInverseNonnegative : 0ℚ ≤ marginInverse
    coefficientNonnegative : 0ℚ ≤ coefficient
    gammaNonnegative : 0ℚ ≤ gamma
    tubeResponseNonnegative : 0ℚ ≤ tubeResponse

    marginInverseIdentity : marginInverse * margin ≡ 1ℚ

    cumulativeTubeBudget :
      margin * cumulativeDirect
      ≤ (Cubic.twoℚ * coefficient * Sixth.cube gamma) * tubeWidth

    tubeWidthBelowInput :
      tubeWidth ≤ tubeResponse * inputDistance

open DirectTubeToInputSensitivity public

directSensitivityConstant : DirectTubeToInputSensitivity → ℚ
directSensitivityConstant dataSet =
  marginInverse dataSet
    * (Cubic.twoℚ * coefficient dataSet * Sixth.cube (gamma dataSet))
    * tubeResponse dataSet

directTubeBudgetGivesInputSensitivity :
  (dataSet : DirectTubeToInputSensitivity) →
  cumulativeDirect dataSet
  ≤ directSensitivityConstant dataSet * inputDistance dataSet
directTubeBudgetGivesInputSensitivity dataSet =
  let
    inv = marginInverse dataSet
    m = margin dataSet
    C = coefficient dataSet
    g = gamma dataSet
    T = tubeResponse dataSet
    w = tubeWidth dataSet
    d = inputDistance dataSet
    s = cumulativeDirect dataSet
    amplitude = Cubic.twoℚ * C * Sixth.cube g
    prefactor = inv * amplitude

    twoNN : 0ℚ ≤ Cubic.twoℚ
    twoNN = ℚP.nonNegative⁻¹ Cubic.twoℚ

    gammaCubeNN : 0ℚ ≤ Sixth.cube g
    gammaCubeNN =
      mulNN
        (mulNN (gammaNonnegative dataSet) (gammaNonnegative dataSet))
        (gammaNonnegative dataSet)

    amplitudeNN : 0ℚ ≤ amplitude
    amplitudeNN =
      mulNN
        (mulNN twoNN (coefficientNonnegative dataSet))
        gammaCubeNN

    scaledBudget = Norm.scaleNonnegative
      inv (marginInverseNonnegative dataSet)
      (cumulativeTubeBudget dataSet)

    associated : inv * (m * s) ≡ (inv * m) * s
    associated = sym (ℚP.*-assoc inv m s)

    cancelled : (inv * m) * s ≡ s
    cancelled =
      subst
        (λ factor → factor * s ≡ s)
        (sym (marginInverseIdentity dataSet))
        (ℚP.*-identityˡ s)

    cancelMargin : inv * (m * s) ≡ s
    cancelMargin = trans associated cancelled

    afterCancel : s ≤ inv * (amplitude * w)
    afterCancel =
      subst
        (λ left → left ≤ inv * (amplitude * w))
        cancelMargin scaledBudget

    afterReassociate : s ≤ prefactor * w
    afterReassociate =
      subst
        (λ upper → s ≤ upper)
        (ℚRing.solve-∀ inv amplitude w)
        afterCancel

    prefactorNN : 0ℚ ≤ prefactor
    prefactorNN = mulNN (marginInverseNonnegative dataSet) amplitudeNN

    widthScaled : prefactor * w ≤ prefactor * (T * d)
    widthScaled = Norm.scaleNonnegative
      prefactor prefactorNN (tubeWidthBelowInput dataSet)

    throughWidth : s ≤ prefactor * (T * d)
    throughWidth = ℚP.≤-trans afterReassociate widthScaled
  in
  subst
    (λ upper → s ≤ upper)
    (ℚRing.solve-∀ inv amplitude T d)
    throughWidth

rowADirectTubeToInputSensitivityAlgebraLevel : ProofLevel
rowADirectTubeToInputSensitivityAlgebraLevel = machineChecked

literalRowATubeWidthResponseToInverseSquareInputLevel : ProofLevel
literalRowATubeWidthResponseToInverseSquareInputLevel = conditional
