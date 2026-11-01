module DASHI.Physics.YangMills.BalabanCMP119FactorizedMarkedBudgetVanishesValidation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119FactorizedMarkedBudgetVanishesExact as V
stepToDensityVanishesOwned : V.cmp119MarkedStepToDensityVanishingCompilerLevel ≡ machineChecked
stepToDensityVanishesOwned = refl
densityConvergenceOwned : V.cmp119FactorizedDensityConvergenceFromStepsLevel ≡ machineChecked
densityConvergenceOwned = refl
