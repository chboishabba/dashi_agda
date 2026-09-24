{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRouteSModeSelectedSpectralGapCompilerValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayRouteSModeSelectedSpectralGapCompilerExact as Route

noArbitrarySpectralEnvelope :
  Route.arbitraryObservableSpectralEnvelopeRequired ≡ false
noArbitrarySpectralEnvelope = refl

noSeparateOverlapLeaf :
  Route.separatePositiveOverlapLeafRequired ≡ false
noSeparateOverlapLeaf = refl

noSeparateSpectralLowerLeaf :
  Route.separateSpectralLowerInequalityLeafRequired ≡ false
noSeparateSpectralLowerLeaf = refl

sameHamiltonianDecompositionRemainsPhysical :
  Route.sameHamiltonianSpectralDecompositionStillPhysical ≡ true
sameHamiltonianDecompositionRemainsPhysical = refl

energyDecayOrderingRemainsPhysical :
  Route.energyToDecayOrderingStillPhysical ≡ true
energyDecayOrderingRemainsPhysical = refl

promotionFailClosed :
  Route.clayPromotion ≡ false
promotionFailClosed = refl
