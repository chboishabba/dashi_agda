{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119TenFinitePhysicalCompositeDerivativeValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.GRQFTCMP119CorrectedD1MaxCutExact as D1
import DASHI.Physics.Foundations.CMP119TenFinitePhysicalCompositeDerivativeExact as Ten

oldD1bRemoved :
  D1.oldD1bTangentFibreEqualityRequired ≡ false
oldD1bRemoved = refl

sequentialTangentCompilerOwned :
  D1.round256SequentialTangentCompositionCompilerOwned ≡ true
sequentialTangentCompilerOwned = refl

tenReadoutAddsNoSecondStressLaw :
  Ten.tenDerivativeReadoutIntroducesSecondStressLaw ≡ false
tenReadoutAddsNoSecondStressLaw = refl
