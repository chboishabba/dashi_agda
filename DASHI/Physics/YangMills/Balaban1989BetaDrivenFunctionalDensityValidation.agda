module DASHI.Physics.YangMills.Balaban1989BetaDrivenFunctionalDensityValidation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenFunctionalDensityExact as F
densityFunctionalByConstruction : F.functionalDensityIsLiteralFunctionLevel ≡ machineChecked
densityFunctionalByConstruction = refl
betaCompilerOwned : F.functionalDensityBetaFlowCompilerLevel ≡ machineChecked
betaCompilerOwned = refl
