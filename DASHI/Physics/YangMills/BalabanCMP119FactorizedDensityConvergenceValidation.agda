module DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityConvergenceValidation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityConvergenceExact as C
convergenceCompilerOwned : C.cmp119FactorizedDensityConvergenceCompilerLevel ≡ machineChecked
convergenceCompilerOwned = refl
