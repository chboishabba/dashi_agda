module DASHI.Physics.YangMills.BalabanRowADirectQFromTubeExact where

------------------------------------------------------------------------
-- ROW A: SIXTH-ORDER TUBE BUDGET -> EXPLICIT DIRECT LIPSCHITZ CONSTANT
--
-- Upstream exact algebra gives a cumulative direct sensitivity estimate
--
--   bStar * S_direct <= (2 C gamma^3) * tubeWidth.
--
-- If the generated tube width itself is Lipschitz in the shooting input,
--
--   tubeWidth <= T * |delta u|,
--
-- and bInv*bStar=1, then
--
--   S_direct <= qDirect * |delta u|,
--   qDirect = bInv * (2 C gamma^3) * T.
--
-- This module proves that ordered-rational implication exactly.  The physical
-- tasks are reduced to the source values C,T,bStar and the same-tube
-- identification; no Banach/fixed-point algebra is repeated here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

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

    twoNN : 0ℚ ≤ Cubic.twoℚ
    twoNN = ℚP.nonNegative⁻¹ Cubic.twoℚ

    gammaCubeNN : 0ℚ ≤ Sixth.cube g
    gammaCubeNN =
      mulNN
        (mulNN (gammaNonnegative dataSet) (gammaNonnegative dataSet))
        (gammaNonnegative dataSet)

    amplitudeNN :
      0ℚ ≤ Cubic.twoℚ * C * Sixth.cube g
    amplitudeNN =
      mulNN
        (mulNN twoNN (coefficientNonnegative dataSet))
        gammaCubeNN

    scaledBudget = Norm.scaleNonnegative
      inv (marginInverseNonnegative dataSet)
      (cumulativeTubeBudget dataSet)

    cancelMargin :
      inv * (m * s) ≡ s
    cancelMargin =
      subst
        (λ left → left * s ≡ s)
        (marginInverseIdentity dataSet)
        (ℚP.*-identityˡ s)

    afterCancel :
      s ≤ inv * ((Cubic.twoℚ * C * Sixth.cube g) * w)
    afterCancel =
      subst
        (λ left → left ≤ inv * ((Cubic.twoℚ * C * Sixth.cube g) * w))
        cancelMargin scaledBudget

    prefactorNN :
      0ℚ ≤ inv * (Cubic.twoℚ * C * Sixth.cube g)
    prefactorNN = mulNN (marginInverseNonnegative dataSet) amplitudeNN

    widthScaled = Norm.scaleNonnegative
      (inv * (Cubic.twoℚ * C * Sixth.cube g))
      prefactorNN
      (tubeWidthBelowInput dataSet)
  in
  ℚP.≤-trans
    afterCancel
    (subst
      (λ upper →
        inv * ((Cubic.twoℚ * C * Sixth.cube g) * w) ≤ upper)
      (ℚRing.solve-∀ inv C g T w d)
      widthScaled)

rowADirectTubeToInputSensitivityAlgebraLevel : ProofLevel
rowADirectTubeToInputSensitivityAlgebraLevel = machineChecked

literalRowATubeWidthResponseToInverseSquareInputLevel : ProofLevel
literalRowATubeWidthResponseToInverseSquareInputLevel = conditional
