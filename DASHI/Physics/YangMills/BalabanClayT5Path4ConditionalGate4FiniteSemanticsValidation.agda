module DASHI.Physics.YangMills.BalabanClayT5Path4ConditionalGate4FiniteSemanticsValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5Path4ConditionalGate4FiniteSemanticsExact as Path4

conditionalFiniteSemanticsClosed :
  Path4.path4ConditionalGate4FiniteSemanticsCompilerLevel ≡ machineChecked
conditionalFiniteSemanticsClosed = refl

conditionalExpectationIntegralClosed :
  Path4.path4ConditionalGate4ExpectationIntegralCompilerLevel ≡ machineChecked
conditionalExpectationIntegralClosed = refl

observableEvaluationRemainsPhysical :
  Path4.path4ConditionalObservableEvaluationLevel ≡ conditional
observableEvaluationRemainsPhysical = refl
