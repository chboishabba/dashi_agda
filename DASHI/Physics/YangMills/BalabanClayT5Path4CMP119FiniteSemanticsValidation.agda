module DASHI.Physics.YangMills.BalabanClayT5Path4CMP119FiniteSemanticsValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5Path4CMP119FiniteSemanticsExact as Path4

finiteSemanticsCompilerClosed :
  Path4.path4CMP119FiniteSemanticsCompilerLevel ≡ machineChecked
finiteSemanticsCompilerClosed = refl

expectationIntegralCompilerClosed :
  Path4.path4CMP119ExpectationIntegralCompilerLevel ≡ machineChecked
expectationIntegralCompilerClosed = refl

observableEvaluationRemainsPhysical :
  Path4.path4CMP119ObservableEvaluationLevel ≡ conditional
observableEvaluationRemainsPhysical = refl
