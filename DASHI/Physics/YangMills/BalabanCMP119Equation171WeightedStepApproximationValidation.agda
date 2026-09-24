module DASHI.Physics.YangMills.BalabanCMP119Equation171WeightedStepApproximationValidation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119Equation171WeightedStepApproximationExact as S
stepErrorOwned : S.cmp119Equation171WeightedStepErrorCompilerLevel ≡ machineChecked
stepErrorOwned = refl
factorizedApproximationOwned : S.cmp119Equation171ToFactorizedApproximationCompilerLevel ≡ machineChecked
factorizedApproximationOwned = refl
