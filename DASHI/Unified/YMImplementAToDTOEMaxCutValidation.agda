{-# OPTIONS --safe #-}
module DASHI.Unified.YMImplementAToDTOEMaxCutValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unified.YMImplementAToDTOEMaxCutExact as AD
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as A443
import DASHI.Physics.YangMills.BalabanCMP119ReflectionMaxCut20261002Exact as B
import DASHI.Physics.YangMills.BalabanCMP119LiteralResidualWeldMaxCut20261002Exact as C
import DASHI.Physics.YangMills.YangMillsProjectiveCylinderMeasureRepresentationRound534Exact as D534
import DASHI.Unified.BalabanR559TOEMaxCutExact as Joint
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound6Ledger as Gate4Ledger
import DASHI.Physics.YangMills.CompactLieProofLevel as Proof
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Unified.Physics as Physics

------------------------------------------------------------------------
-- Canonical facade reachability.
------------------------------------------------------------------------

rootReceiptMatches :
  TOE.toeYMImplementAToDMaxCutReceipt
  ≡ AD.canonicalYMImplementAToDTOEMaxCutReceipt
rootReceiptMatches = refl

unifierReceiptMatches :
  Unifier.unifierYMImplementAToDMaxCutReceipt
  ≡ AD.canonicalYMImplementAToDTOEMaxCutReceipt
unifierReceiptMatches = refl

physicsReceiptMatches :
  Physics.yangMillsImplementAToDMaxCutReceipt
  ≡ AD.canonicalYMImplementAToDTOEMaxCutReceipt
physicsReceiptMatches = refl

------------------------------------------------------------------------
-- Representative canonical-owner checks.
------------------------------------------------------------------------

aDensityCompilerIsR443 :
  AD.aDensityInvariantCompiler AD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ A443.round443WilsonActionToDensityInvariantCompilerLevel
aDensityCompilerIsR443 = refl

bReflectionCutIsCanonical :
  AD.bReflectionCutCompiler AD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ B.cmp119ReflectionMaxCutCompilerLevel
bReflectionCutIsCanonical = refl

cResidualWeldIsCanonical :
  AD.cResidualWeldCompiler AD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ C.literalResidualWeldCompilerLevel
cResidualWeldIsCanonical = refl

dProjectiveCompilerIsR534 :
  AD.dProjectiveRepresentationCompiler
    AD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ D534.round534ProjectiveRepresentationCompilerLevel
dProjectiveCompilerIsR534 = refl

------------------------------------------------------------------------
-- Exact scope and non-promotion.
------------------------------------------------------------------------

gate4CountIs58 :
  AD.gate4UnresolvedCount AD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ 58
gate4CountIs58 =
  AD.gate4UnresolvedCountIs58 AD.canonicalYMImplementAToDTOEMaxCutReceipt

gate4PaidReductionMatchesJoint :
  AD.gate4PaidReductionLevel AD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ Gate4Ledger.physicalClosureRound6LedgerLevel
gate4PaidReductionMatchesJoint = refl


gate4PaidReductionLedgerIsMachineChecked :
  Proof.promotable
    (AD.gate4PaidReductionLevel AD.canonicalYMImplementAToDTOEMaxCutReceipt)
  ≡ true
gate4PaidReductionLedgerIsMachineChecked =
  Proof.machineCheckedPromotes

gate4InhabitantsRemainConditional :
  Proof.promotable
    (AD.gate4InhabitantsLevel AD.canonicalYMImplementAToDTOEMaxCutReceipt)
  ≡ false
gate4InhabitantsRemainConditional =
  Proof.conditionalDoesNotSelfPromote

rootContinuumStillBlocked :
  AD.publishedContinuumPromotion AD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ false
rootContinuumStillBlocked =
  TOE.toeYMImplementAToDPublishedContinuumStillBlocked

unifierContinuumStillBlocked :
  AD.publishedContinuumPromotion AD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ false
unifierContinuumStillBlocked =
  Unifier.unifierYMImplementAToDPublishedContinuumStillBlocked

physicsContinuumStillBlocked :
  AD.publishedContinuumPromotion AD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ false
physicsContinuumStillBlocked =
  Physics.yangMillsImplementAToDPublishedContinuumStillBlocked

rootMassGapStillBlocked :
  AD.continuumMassGapPromotion AD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ false
rootMassGapStillBlocked =
  TOE.toeYMImplementAToDContinuumMassGapStillBlocked

unifierMassGapStillBlocked :
  AD.continuumMassGapPromotion AD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ false
unifierMassGapStillBlocked =
  Unifier.unifierYMImplementAToDContinuumMassGapStillBlocked

physicsMassGapStillBlocked :
  AD.continuumMassGapPromotion AD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ false
physicsMassGapStillBlocked =
  Physics.yangMillsImplementAToDContinuumMassGapStillBlocked

rootClayStillBlocked :
  AD.clayPromotion AD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ false
rootClayStillBlocked =
  TOE.toeYMImplementAToDClayStillBlocked

unifierClayStillBlocked :
  AD.clayPromotion AD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ false
unifierClayStillBlocked =
  Unifier.unifierYMImplementAToDClayStillBlocked

physicsClayStillBlocked :
  AD.clayPromotion AD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ false
physicsClayStillBlocked =
  Physics.yangMillsImplementAToDClayStillBlocked

rootScaleTransferPromotionEliminates :
  Joint.ScaleTransferPromotion → ⊥
rootScaleTransferPromotionEliminates =
  TOE.toeYMImplementAToDScaleTransferNonPromotion

unifierScaleTransferPromotionEliminates :
  Joint.ScaleTransferPromotion → ⊥
unifierScaleTransferPromotionEliminates =
  Unifier.unifierYMImplementAToDScaleTransferNonPromotion

physicsScaleTransferPromotionEliminates :
  Joint.ScaleTransferPromotion → ⊥
physicsScaleTransferPromotionEliminates =
  Physics.yangMillsImplementAToDScaleTransferNonPromotion
