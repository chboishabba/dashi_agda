{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2ContinuumWardTransportValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayLevel2ContinuumWardTransportExact as D3

finiteWardAlgebraNotNew :
  D3.finiteWardAlgebraNewPhysicalTheoremInD3 ≡ false
finiteWardAlgebraNotNew = refl

stressProvenanceNotNew :
  D3.generatedActionStressProvenanceNewPhysicalTheoremInD3 ≡ false
stressProvenanceNotNew = refl

sameCurrentContinuumTransportStillPhysical :
  D3.finiteToContinuumSameCurrentTransportStillPhysical ≡ true
sameCurrentContinuumTransportStillPhysical = refl


perturbationIndependentSequenceIsTooWeak :
  D3.perturbationIndependentWardChargeSequenceWouldBeTooWeak ≡ true
perturbationIndependentSequenceIsTooWeak = refl

cutoffIndependentScalarMapNotRequired :
  D3.cutoffIndependentChargeRepresentationMapRequired ≡ false
cutoffIndependentScalarMapNotRequired = refl

promotionFailClosed :
  D3.clayPromotion ≡ false
promotionFailClosed = refl
