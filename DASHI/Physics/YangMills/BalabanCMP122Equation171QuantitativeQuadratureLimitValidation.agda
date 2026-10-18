module DASHI.Physics.YangMills.BalabanCMP122Equation171QuantitativeQuadratureLimitValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP122Equation171QuantitativeQuadratureLimitExact as Q

quantitativeQuadratureCompilerOwned :
  Q.equation171QuantitativeQuadratureCompilerLevel ≡ machineChecked
quantitativeQuadratureCompilerOwned = refl

refinementLimitCompilerOwned :
  Q.equation171QuantitativeRefinementLimitCompilerLevel ≡ machineChecked
refinementLimitCompilerOwned = refl

cellDecompositionStillPhysical :
  Q.literalEquation171CellDecompositionLevel ≡ conditional
cellDecompositionStillPhysical = refl

oscillationVanishingStillAnalytic :
  Q.literalEquation171OscillationBudgetVanishesLevel ≡ conditional
oscillationVanishingStillAnalytic = refl

discrepancyVanishingStillAnalytic :
  Q.literalEquation171DiscrepancyBudgetVanishesLevel ≡ conditional
discrepancyVanishingStillAnalytic = refl
