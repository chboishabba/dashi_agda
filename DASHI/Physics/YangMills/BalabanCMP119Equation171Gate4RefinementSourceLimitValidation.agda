module DASHI.Physics.YangMills.BalabanCMP119Equation171Gate4RefinementSourceLimitValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119Equation171Gate4RefinementSourceLimitExact as L

sourceApplicationLimitCompilerOwned :
  L.cmp119SourceApplicationQuadratureLimitCompilerLevel ≡ machineChecked
sourceApplicationLimitCompilerOwned = refl

selectedDensityLimitCompilerOwned :
  L.cmp119SelectedDensityQuadratureLimitCompilerLevel ≡ machineChecked
selectedDensityLimitCompilerOwned = refl

sourceApplicationMeaningStillPhysical :
  L.literalCMP119ApplicationIsEquation171MassLimitLevel ≡ conditional
sourceApplicationMeaningStillPhysical = refl
