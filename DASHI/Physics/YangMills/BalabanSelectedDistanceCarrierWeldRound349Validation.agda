{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedDistanceCarrierWeldRound349Validation where

------------------------------------------------------------------------
-- RED-first validation root for the R346 D_time recut.
--
-- R304 already proves distance=time on the exact R300-selected spectral pair,
-- but on the older R284 direct-shell distance carrier.  R349 must therefore
-- reduce fresh time semantics to one SAME-pair distance-carrier weld between
-- R318 and R284.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanSelectedDistanceCarrierWeldRound349Exact as R349

r304SelectedDistanceTimeDonorOwned : Bool
r304SelectedDistanceTimeDonorOwned = R349.r304SelectedDistanceTimeDonorOwned

r304SelectedDistanceTimeDonorOwnedIsTrue :
  r304SelectedDistanceTimeDonorOwned ≡ true
r304SelectedDistanceTimeDonorOwnedIsTrue =
  R349.r304SelectedDistanceTimeDonorOwnedIsTrue

selectedDistanceCarrierWeldLevel : ProofLevel
selectedDistanceCarrierWeldLevel = R349.selectedDistanceCarrierWeldLevel

freshSelectedDistanceTimeAnalysisRequired : Bool
freshSelectedDistanceTimeAnalysisRequired = R349.freshSelectedDistanceTimeAnalysisRequired

freshSelectedDistanceTimeAnalysisRequiredIsFalse :
  freshSelectedDistanceTimeAnalysisRequired ≡ false
freshSelectedDistanceTimeAnalysisRequiredIsFalse =
  R349.freshSelectedDistanceTimeAnalysisRequiredIsFalse

selectedPairChangedByTransport : Bool
selectedPairChangedByTransport = R349.selectedPairChangedByTransport

selectedPairChangedByTransportIsFalse : selectedPairChangedByTransport ≡ false
selectedPairChangedByTransportIsFalse = R349.selectedPairChangedByTransportIsFalse

clayPromotion : Bool
clayPromotion = R349.clayPromotion

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = R349.clayPromotionIsFalse
