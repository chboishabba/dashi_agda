{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityPostNormalizationReuseMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.ExoticGravity.AntigravityPostNormalizationMaxCutExact as Prior
import DASHI.Physics.Foundations.CMP119AntigravityR136ToStaticVacuumPromotionExact as R136Static
import DASHI.Physics.Foundations.CMP119AntigravityR136StaticPairToDifferentialExact as R136Pair

------------------------------------------------------------------------
-- POST-NORMALIZATION REUSE MAX-CUT
--
-- The old S/D/R fork remains useful at source acquisition, but the physical
-- promotion stages are not independent once the R136/Local-C route has paid
-- same-state Lorentzian vacuum response.
--
-- One R136 endpoint + affine V->rho calibration -> static receipt.
-- Two R136 endpoints + one shared affine calibration/common renormalization
-- convention -> differential receipt.
--
-- Thus R is an OPTIONAL producer for S/D promotion; it is not a prerequisite
-- for acquiring the source normalization coordinate, and S/D do not require an
-- independent metric-response theorem after the corresponding R receipt exists.
------------------------------------------------------------------------

sourceAcquisitionRoutesRemainAlternative : Bool
sourceAcquisitionRoutesRemainAlternative = true

r136VacuumReadoutCanProduceStaticPromotion : Bool
r136VacuumReadoutCanProduceStaticPromotion =
  R136Static.r136CanProduceStaticReceiptAfterAffineCalibration

independentStaticMetricResponseReceiptRequiredAfterR136Promotion : Bool
independentStaticMetricResponseReceiptRequiredAfterR136Promotion =
  R136Static.independentStaticMetricResponseReceiptRequiredAfterR136Promotion

r136CommonPairCanProduceDifferentialPromotion : Bool
r136CommonPairCanProduceDifferentialPromotion =
  R136Pair.r136CanProduceStaticAndDifferentialConsumersWithOneSharedCalibration

independentDeltaSameObjectTheoremRequiredAfterCommonR136Pair : Bool
independentDeltaSameObjectTheoremRequiredAfterCommonR136Pair =
  R136Pair.independentDeltaSameObjectTheoremRequiredAfterCommonR136Pair

sharedAffineNormalizationToGravityCalibrationStillRequired : Bool
sharedAffineNormalizationToGravityCalibrationStillRequired = true

commonCosmologicalRenormalizationConventionStillRequired : Bool
commonCosmologicalRenormalizationConventionStillRequired = true

r136PinnedFiniteAnchorAndTailStillRequiredBeforeReuse : Bool
r136PinnedFiniteAnchorAndTailStillRequiredBeforeReuse =
  Prior.continuumPinnedFiniteAnchorAndTailBoundStillRequired

r136StrictFinitePlusTailMarginStillRequiredBeforeReuse : Bool
r136StrictFinitePlusTailMarginStillRequiredBeforeReuse =
  Prior.continuumStrictFinitePlusTailMarginStillRequired

r136SameStateEuclideanLorentzianStressStillRequiredBeforeReuse : Bool
r136SameStateEuclideanLorentzianStressStillRequiredBeforeReuse = true

scalarKottlerResponseStillDoesNotConstructTTMode : Bool
scalarKottlerResponseStillDoesNotConstructTTMode = true

record PostNormalizationReuseFrontier : Set where
  constructor post-normalization-reuse-frontier
  field
    sourceAcquisitionStillForked : Bool
    r136MayPayStaticPromotion : Bool
    separateStaticMetricReceiptAfterR136 : Bool
    r136PairMayPayDifferentialPromotion : Bool
    separateDeltaSameObjectTheoremAfterR136Pair : Bool
    sharedAffineCalibrationStillPhysical : Bool
    sharedRenormalizationConventionStillPhysical : Bool
    r136FiniteAnchorTailStillPhysical : Bool
    r136LorentzianContinuationStillPhysical : Bool
    ttProducerStillIndependent : Bool

canonicalPostNormalizationReuseFrontier : PostNormalizationReuseFrontier
canonicalPostNormalizationReuseFrontier =
  post-normalization-reuse-frontier
    true true false true false true true true true true

representationOnlyPromotionDebtRemainsAfterR136Reuse : Bool
representationOnlyPromotionDebtRemainsAfterR136Reuse = false

representationOnlyPromotionDebtRemainsAfterR136ReuseIsFalse :
  representationOnlyPromotionDebtRemainsAfterR136Reuse ≡ false
representationOnlyPromotionDebtRemainsAfterR136ReuseIsFalse = refl
