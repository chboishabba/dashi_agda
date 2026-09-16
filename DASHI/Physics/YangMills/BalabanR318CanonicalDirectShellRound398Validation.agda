{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanR318CanonicalDirectShellRound398Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanR318CanonicalDirectShellRound398Exact as R398

round398NoIndependentR284Distance :
  R398.independentR284DistanceCarrierRequired ≡ false
round398NoIndependentR284Distance = refl

round398NoCrossCarrierWeld :
  R398.r349CrossCarrierDistanceWeldRequiredOnCanonicalConstruction ≡ false
round398NoCrossCarrierWeld = refl

round398TimeSemanticsRetained :
  R398.selectedPhysicalDistanceTimeSemanticsStillProofBearing ≡ true
round398TimeSemanticsRetained = refl

round398NoFreshDecayEstimate :
  R398.freshYMDecayEstimateIntroduced ≡ false
round398NoFreshDecayEstimate = refl

round398NoClayPromotion : R398.clayPromotion ≡ false
round398NoClayPromotion = refl
