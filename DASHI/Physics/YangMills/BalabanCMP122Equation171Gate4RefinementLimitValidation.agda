module DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4RefinementLimitValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4RefinementLimitExact as L

sliceCompilerOwned :
  L.equation171Gate4RefinementSliceCompilerLevel ≡ machineChecked
sliceCompilerOwned = refl

sourceMassLimitCompilerOwned :
  L.equation171SourceMassQuadratureLimitCompilerLevel ≡ machineChecked
sourceMassLimitCompilerOwned = refl

productHaarQuadratureStillAnalytic :
  L.literalEquation171ProductHaarQuadratureLimitLevel ≡ conditional
productHaarQuadratureStillAnalytic = refl
