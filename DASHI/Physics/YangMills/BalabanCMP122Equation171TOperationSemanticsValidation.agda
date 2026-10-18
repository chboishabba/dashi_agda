module DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as E

equation171TOperationCompilerOwned :
  E.cmp122Equation171TOperationSemanticsCompilerLevel ≡ machineChecked
equation171TOperationCompilerOwned = refl

literalEquation171FiniteRealizationRemainsPhysical :
  E.literalCMP122Equation171FiniteRealizationLevel ≡ conditional
literalEquation171FiniteRealizationRemainsPhysical = refl
