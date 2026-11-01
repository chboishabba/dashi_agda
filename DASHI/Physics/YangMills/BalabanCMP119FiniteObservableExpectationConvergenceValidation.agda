module DASHI.Physics.YangMills.BalabanCMP119FiniteObservableExpectationConvergenceValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119FiniteObservableExpectationConvergenceExact as E

expectationErrorCompilerOwned :
  E.cmp119FiniteObservableExpectationErrorCompilerLevel ≡ machineChecked
expectationErrorCompilerOwned = refl

expectationConvergenceCompilerOwned :
  E.cmp119FiniteObservableExpectationConvergenceCompilerLevel ≡ machineChecked
expectationConvergenceCompilerOwned = refl

physicalMeasureWeldStillOpen :
  E.literalCMP119DensityToFiniteMeasureExpectationWeldLevel ≡ conditional
physicalMeasureWeldStillOpen = refl
