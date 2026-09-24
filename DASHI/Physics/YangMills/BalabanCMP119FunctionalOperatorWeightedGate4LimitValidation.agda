module DASHI.Physics.YangMills.BalabanCMP119FunctionalOperatorWeightedGate4LimitValidation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119FunctionalOperatorWeightedGate4LimitExact as L
limitCompilerOwned : L.functionalOperatorWeightedLimitCompilerLevel ≡ machineChecked
limitCompilerOwned = refl
f1aGone : L.functionalOperatorF1aEliminatedLevel ≡ machineChecked
f1aGone = refl
factorizedSourceStillPhysical : L.literalCMP119FactorizedTOperationToEquation171Level ≡ conditional
factorizedSourceStillPhysical = refl
