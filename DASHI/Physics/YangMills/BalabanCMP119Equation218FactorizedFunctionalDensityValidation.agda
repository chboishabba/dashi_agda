module DASHI.Physics.YangMills.BalabanCMP119Equation218FactorizedFunctionalDensityValidation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119Equation218FactorizedFunctionalDensityExact as F
densityAlgebraOwned : F.equation218FactorizedFiniteAlgebraLevel ≡ machineChecked
densityAlgebraOwned = refl
componentProductOwned : F.equation219ComponentProductLevel ≡ machineChecked
componentProductOwned = refl
orderedStepProductOwned : F.equation220OrderedStepProductLevel ≡ machineChecked
orderedStepProductOwned = refl
functionalDensityCompilerOwned : F.equation218FunctionalDensityCompilerLevel ≡ machineChecked
functionalDensityCompilerOwned = refl
