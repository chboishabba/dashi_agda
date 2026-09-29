{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayMeasureCompleteResidualRound540Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayMeasureCompleteResidualRound540Exact as R540
open import DASHI.Physics.YangMills.CompactLieProofLevel

residualCountIsTwentySeven :
  R540.residualLeafCount ≡ 27
residualCountIsTwentySeven = refl

positiveProbabilityExplicit :
  R540.positiveCylinderProbabilityRequired ≡ true
positiveProbabilityExplicit = refl

booleanAlgebraExplicit :
  R540.cylinderBooleanAlgebraRequired ≡ true
booleanAlgebraExplicit = refl

wholeProjectiveExplicit :
  R540.wholeProjectiveExtensionRequired ≡ true
wholeProjectiveExplicit = refl

singleCutoffPruned :
  R540.selectedSingleCutoffExtensionAllowedAsPreferredRoute ≡ false
singleCutoffPruned = refl

noOpaqueEndpointSemantics :
  R540.opaqueEndpointSemanticLeavesRemaining ≡ false
noOpaqueEndpointSemantics = refl
