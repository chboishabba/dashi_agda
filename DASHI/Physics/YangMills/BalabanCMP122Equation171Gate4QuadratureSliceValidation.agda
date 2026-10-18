module DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4QuadratureSliceValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4QuadratureSliceExact as S

sliceCompilerOwned :
  S.equation171Gate4QuadratureSliceCompilerLevel ≡ machineChecked
sliceCompilerOwned = refl

sliceFoldCompilerOwned :
  S.equation171Gate4SliceFoldCompilerLevel ≡ machineChecked
sliceFoldCompilerOwned = refl

fibreStillPhysical :
  S.literalEquation171SliceFibreLevel ≡ conditional
fibreStillPhysical = refl

selectorStillPhysical :
  S.literalEquation171SliceSelectorLevel ≡ conditional
selectorStillPhysical = refl

integrandStillPhysical :
  S.literalEquation171SliceIntegrandLevel ≡ conditional
integrandStillPhysical = refl
