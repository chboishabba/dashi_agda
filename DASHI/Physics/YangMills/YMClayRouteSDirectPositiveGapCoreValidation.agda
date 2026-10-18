{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRouteSDirectPositiveGapCoreValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayRouteSDirectPositiveGapCoreExact as Route

noOldRateRecord :
  Route.oldModeIndexedRateRecordMandatory ≡ false
noOldRateRecord = refl

noArbitraryClusteringEnvelope :
  Route.arbitraryClusteringEnvelopeMandatory ≡ false
noArbitraryClusteringEnvelope = refl

noSeparateOverlapLeaf :
  Route.separatePositiveOverlapLeafMandatory ≡ false
noSeparateOverlapLeaf = refl

noSeparateSpectralLowerLeaf :
  Route.separateSpectralLowerLeafMandatory ≡ false
noSeparateSpectralLowerLeaf = refl

sameHamiltonianDecompositionStillPhysical :
  Route.sameHamiltonianPositiveSpectralDecompositionStillPhysical ≡ true
sameHamiltonianDecompositionStillPhysical = refl

transferCoordinateStillPhysical :
  Route.transferEnergyDecayCoordinateStillPhysical ≡ true
transferCoordinateStillPhysical = refl

modeRatioWeldStillPhysical :
  Route.modeRatioSameCoordinateWeldStillPhysical ≡ true
modeRatioWeldStillPhysical = refl

gapCoreCompilerOwned :
  Route.positiveCandidateAndNoSubgapAfterPaymentsCompilerOwned ≡ true
gapCoreCompilerOwned = refl

promotionFailClosed :
  Route.clayPromotion ≡ false
promotionFailClosed = refl
