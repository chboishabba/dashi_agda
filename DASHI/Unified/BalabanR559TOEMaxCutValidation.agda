{-# OPTIONS --safe #-}
module DASHI.Unified.BalabanR559TOEMaxCutValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Empty using (⊥)

import DASHI.Unified.BalabanR559TOEMaxCutExact as Joint
import DASHI.Physics.Closure.BalabanRGScaleTransferFrontierReceipt as RGNonPromotion
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Unified.Physics as Physics
import DASHI.Unified.Everything as Everything

------------------------------------------------------------------------
-- Canonical consumer reachability.
------------------------------------------------------------------------

rootReceiptMatches :
  TOE.toeBalabanR559MaxCutReceipt
  ≡ Joint.canonicalBalabanR559TOEMaxCutReceipt
rootReceiptMatches = refl

unifierReceiptMatches :
  Unifier.unifierBalabanR559MaxCutReceipt
  ≡ Joint.canonicalBalabanR559TOEMaxCutReceipt
unifierReceiptMatches = refl

physicsReceiptMatches :
  Physics.yangMillsBalabanR559MaxCutReceipt
  ≡ Joint.canonicalBalabanR559TOEMaxCutReceipt
physicsReceiptMatches = refl

unifiedEverythingReceiptMatches :
  Everything.unifiedBalabanR559MaxCutReceipt
  ≡ Joint.canonicalBalabanR559TOEMaxCutReceipt
unifiedEverythingReceiptMatches = refl

------------------------------------------------------------------------
-- Shared owner checks.
------------------------------------------------------------------------

densityOwnerAgreementIsExact :
  Joint.balabanDensityFlow Joint.canonicalBalabanR559TOEMaxCutReceipt
  ≡ Joint.r559DensityFlow Joint.canonicalBalabanR559TOEMaxCutReceipt
densityOwnerAgreementIsExact =
  Joint.densityOwnerAgreement Joint.canonicalBalabanR559TOEMaxCutReceipt

regularEOwnerAgreementIsExact :
  Joint.balabanRegularELocalization Joint.canonicalBalabanR559TOEMaxCutReceipt
  ≡ Joint.r559RegularELocalization Joint.canonicalBalabanR559TOEMaxCutReceipt
regularEOwnerAgreementIsExact =
  Joint.regularEOwnerAgreement Joint.canonicalBalabanR559TOEMaxCutReceipt

stressMarkedShellOwnerAgreementIsExact :
  Joint.balabanStressMarkedShell Joint.canonicalBalabanR559TOEMaxCutReceipt
  ≡ Joint.r559StressMarkedShell Joint.canonicalBalabanR559TOEMaxCutReceipt
stressMarkedShellOwnerAgreementIsExact =
  Joint.stressMarkedShellOwnerAgreement Joint.canonicalBalabanR559TOEMaxCutReceipt

stressHilbertOwnerAgreementIsExact :
  Joint.balabanStressHilbertCompiler Joint.canonicalBalabanR559TOEMaxCutReceipt
  ≡ Joint.r559StressHilbertCompiler Joint.canonicalBalabanR559TOEMaxCutReceipt
stressHilbertOwnerAgreementIsExact =
  Joint.stressHilbertOwnerAgreement Joint.canonicalBalabanR559TOEMaxCutReceipt

------------------------------------------------------------------------
-- Fail-closed promotion checks.
------------------------------------------------------------------------

rootContinuumStillOpen :
  Joint.publishedContinuumPromotion Joint.canonicalBalabanR559TOEMaxCutReceipt
  ≡ false
rootContinuumStillOpen =
  TOE.toeBalabanR559PublishedContinuumStillOpen

unifierContinuumStillOpen :
  Joint.publishedContinuumPromotion Joint.canonicalBalabanR559TOEMaxCutReceipt
  ≡ false
unifierContinuumStillOpen =
  Unifier.unifierBalabanR559PublishedContinuumStillOpen

physicsContinuumStillOpen :
  Joint.publishedContinuumPromotion Joint.canonicalBalabanR559TOEMaxCutReceipt
  ≡ false
physicsContinuumStillOpen =
  Physics.yangMillsBalabanR559PublishedContinuumStillOpen

rootMassGapStillBlocked :
  Joint.continuumMassGapPromotion Joint.canonicalBalabanR559TOEMaxCutReceipt
  ≡ false
rootMassGapStillBlocked =
  TOE.toeBalabanR559ContinuumMassGapStillBlocked

unifierMassGapStillBlocked :
  Joint.continuumMassGapPromotion Joint.canonicalBalabanR559TOEMaxCutReceipt
  ≡ false
unifierMassGapStillBlocked =
  Unifier.unifierBalabanR559ContinuumMassGapStillBlocked

physicsMassGapStillBlocked :
  Joint.continuumMassGapPromotion Joint.canonicalBalabanR559TOEMaxCutReceipt
  ≡ false
physicsMassGapStillBlocked =
  Physics.yangMillsBalabanR559ContinuumMassGapStillBlocked

rootClayStillBlocked :
  Joint.clayPromotion Joint.canonicalBalabanR559TOEMaxCutReceipt
  ≡ false
rootClayStillBlocked =
  TOE.toeBalabanR559ClayPromotionStillBlocked

unifierClayStillBlocked :
  Joint.clayPromotion Joint.canonicalBalabanR559TOEMaxCutReceipt
  ≡ false
unifierClayStillBlocked =
  Unifier.unifierBalabanR559ClayPromotionStillBlocked

physicsClayStillBlocked :
  Joint.clayPromotion Joint.canonicalBalabanR559TOEMaxCutReceipt
  ≡ false
physicsClayStillBlocked =
  Physics.yangMillsBalabanR559ClayPromotionStillBlocked


------------------------------------------------------------------------
-- Direct constructive scale-transfer non-promotion reachability.
------------------------------------------------------------------------

rootScaleTransferPromotionEliminates :
  RGNonPromotion.BalabanRGScaleTransferPromotion → ⊥
rootScaleTransferPromotionEliminates =
  TOE.toeBalabanScaleTransferNonPromotion

unifierScaleTransferPromotionEliminates :
  RGNonPromotion.BalabanRGScaleTransferPromotion → ⊥
unifierScaleTransferPromotionEliminates =
  Unifier.unifierBalabanScaleTransferNonPromotion
