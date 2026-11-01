module DASHI.Foundations.BishopCubicRatioWitnessCongruenceExact where

------------------------------------------------------------------------
-- CUBIC RATIO IS INDEPENDENT OF THE CHOSEN POSITIVITY WITNESS
--
-- `q x positive` is implemented by the vendored constructive inverse and thus
-- syntactically carries a proof witness.  Analytic carrier identity must not.
-- This owner proves setoid equality for any two positivity witnesses and lifts
-- it through finite powers.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopCubicTranslationGeometricRatioExact as Ratio
open import DASHI.Physics.YangMills.CompactLieProofLevel

qWitnessCongruent :
  ∀ {x : BishopReal.ℝ}
    (leftPositive rightPositive : BishopReal._<_ BishopReal.0ℝ x) →
  BishopReal._≃_
    (Ratio.q x leftPositive)
    (Ratio.q x rightPositive)
qWitnessCongruent {x} leftPositive rightPositive =
  BishopInverse.⁻¹-cong
    (Ratio.d3Nonzero leftPositive)
    (Ratio.d3Nonzero rightPositive)
    BishopP.≃-refl

powCongruent :
  ∀ {left right : BishopReal.ℝ} →
  BishopReal._≃_ left right →
  ∀ exponent →
  BishopReal._≃_
    (BishopReal.pow left exponent)
    (BishopReal.pow right exponent)
powCongruent equality zero = BishopP.≃-refl
powCongruent {left} {right} equality (suc exponent) =
  BishopP.*-cong
    (powCongruent equality exponent)
    equality

qPowerWitnessCongruent :
  ∀ {x : BishopReal.ℝ}
    (leftPositive rightPositive : BishopReal._<_ BishopReal.0ℝ x) →
  ∀ exponent →
  BishopReal._≃_
    (BishopReal.pow (Ratio.q x leftPositive) exponent)
    (BishopReal.pow (Ratio.q x rightPositive) exponent)
qPowerWitnessCongruent leftPositive rightPositive exponent =
  powCongruent
    (qWitnessCongruent leftPositive rightPositive)
    exponent

bishopCubicRatioWitnessCongruenceLevel : ProofLevel
bishopCubicRatioWitnessCongruenceLevel = machineChecked
