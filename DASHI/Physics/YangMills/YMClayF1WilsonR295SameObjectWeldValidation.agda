{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayF1WilsonR295SameObjectWeldValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayF1WilsonR295SameObjectWeldExact as Weld

carrierEqualityNotIndependent :
  Weld.independentWilsonToR295CarrierEqualityRequired ≡ false
carrierEqualityNotIndependent = refl

r295R296CompilerOwned :
  Weld.r295ToR296CarrierCompilerOwned ≡ true
r295R296CompilerOwned = refl

operationWeldCompilerOwned :
  Weld.wilsonT5OperationWeldCompilerOwnedOncePresentationExists ≡ true
operationWeldCompilerOwned = refl

physicalResidueIsR315Presentation :
  Weld.f1BPhysicalResidueIsR315Presentation ≡ true
physicalResidueIsR315Presentation = refl

promotionFailClosed :
  Weld.clayPromotion ≡ false
promotionFailClosed = refl
