{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedCoefficientAttachmentRound348Validation where

------------------------------------------------------------------------
-- RED-first validation root for the R347 -> R348 Pareto recut.
--
-- R318 already fixes the selected source directions definitionally as
--
--   sourceDirectionOf meaning left/right.
--
-- R348 must therefore keep only the residual same-object theorem:
-- the source/Cauchy coefficient on those already-selected directions is the
-- literal selected mixed-log response consumed by R346.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116SelectedCoefficientAttachmentRound348Exact as R348

selectedJDirectionsAlreadyChosenByR318 : Bool
selectedJDirectionsAlreadyChosenByR318 = R348.selectedJDirectionsAlreadyChosenByR318

selectedJDirectionsAlreadyChosenByR318IsTrue :
  selectedJDirectionsAlreadyChosenByR318 ≡ true
selectedJDirectionsAlreadyChosenByR318IsTrue =
  R348.selectedJDirectionsAlreadyChosenByR318IsTrue

selectedCoefficientSameObjectLevel : ProofLevel
selectedCoefficientSameObjectLevel = R348.selectedCoefficientSameObjectLevel

freshDirectionSelectionRequired : Bool
freshDirectionSelectionRequired = R348.freshDirectionSelectionRequired

freshDirectionSelectionRequiredIsFalse : freshDirectionSelectionRequired ≡ false
freshDirectionSelectionRequiredIsFalse = R348.freshDirectionSelectionRequiredIsFalse

boundaryComparisonStillIndependent : Bool
boundaryComparisonStillIndependent = R348.boundaryComparisonStillIndependent

boundaryComparisonStillIndependentIsTrue : boundaryComparisonStillIndependent ≡ true
boundaryComparisonStillIndependentIsTrue = R348.boundaryComparisonStillIndependentIsTrue

selectedDistanceTimeStillIndependent : Bool
selectedDistanceTimeStillIndependent = R348.selectedDistanceTimeStillIndependent

selectedDistanceTimeStillIndependentIsTrue : selectedDistanceTimeStillIndependent ≡ true
selectedDistanceTimeStillIndependentIsTrue = R348.selectedDistanceTimeStillIndependentIsTrue

clayPromotion : Bool
clayPromotion = R348.clayPromotion

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = R348.clayPromotionIsFalse
