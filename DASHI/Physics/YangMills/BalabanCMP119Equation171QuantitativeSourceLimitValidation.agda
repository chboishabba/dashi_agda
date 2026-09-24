module DASHI.Physics.YangMills.BalabanCMP119Equation171QuantitativeSourceLimitValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119Equation171QuantitativeSourceLimitExact as Q

sourceLimitCompilerOwned :
  Q.cmp119QuantitativeSourceLimitCompilerLevel ≡ machineChecked
sourceLimitCompilerOwned = refl

sourceApplicationMeaningStillPhysical :
  Q.literalCMP119ApplicationEquation171MeaningLevel ≡ conditional
sourceApplicationMeaningStillPhysical = refl
