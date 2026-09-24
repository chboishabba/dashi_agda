module DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationValidation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as A
stepToComponentOwned : A.cmp119OneStepToComponentErrorCompilerLevel ≡ machineChecked
stepToComponentOwned = refl
componentToSequenceOwned : A.cmp119ComponentToSequenceErrorCompilerLevel ≡ machineChecked
componentToSequenceOwned = refl
sequenceToDensityOwned : A.cmp119SequenceToDensityErrorCompilerLevel ≡ machineChecked
sequenceToDensityOwned = refl
