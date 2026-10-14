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
-- The old S/D/R fork remains useful at source acquisition, but two logically
-- different uses of R136 must not be conflated:
--
--   SIGN ROUTE
--     finite R109 anchor/tail + strict margin -> signed R136 response;
--
--   PHYSICAL-RESPONSE REUSE ROUTE
--     actual pinned Local-C terminal producers + affine V->rho calibration
--       -> static receipt;
--     two such endpoints + shared affine calibration/common renormalization
--       -> differential receipt.
--
-- The R109 finite-tail machinery is therefore NOT a prerequisite for consuming
-- an already-produced pinned Local-C terminal as a static/differential physical
-- response.  It remains a real payment only when the consumer additionally
-- needs the independent R136 sign theorem.
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

------------------------------------------------------------------------
-- RESPONSE REUSE VS SIGN-PROOF SEPARATION
------------------------------------------------------------------------

typedPinnedLocalCTerminalStillRequiredForStaticReuse : Bool
typedPinnedLocalCTerminalStillRequiredForStaticReuse = true

r136FiniteAnchorTailRequiredForStaticResponseReuse : Bool
r136FiniteAnchorTailRequiredForStaticResponseReuse = false

r136StrictFinitePlusTailMarginRequiredForStaticResponseReuse : Bool
r136StrictFinitePlusTailMarginRequiredForStaticResponseReuse = false

r136FiniteAnchorTailStillRequiredForIndependentSignRoute : Bool
r136FiniteAnchorTailStillRequiredForIndependentSignRoute =
  Prior.continuumPinnedFiniteAnchorAndTailBoundStillRequired

r136StrictFinitePlusTailMarginStillRequiredForIndependentSignRoute : Bool
r136StrictFinitePlusTailMarginStillRequiredForIndependentSignRoute =
  Prior.continuumStrictFinitePlusTailMarginStillRequired

-- Compatibility surfaces from the older scheduler.  "Before reuse" used to
-- conflate response reuse with the independent sign route.  On the preferred
-- typed Local-C response-reuse route these are now correctly false.
r136PinnedFiniteAnchorAndTailStillRequiredBeforeReuse : Bool
r136PinnedFiniteAnchorAndTailStillRequiredBeforeReuse = false

r136StrictFinitePlusTailMarginStillRequiredBeforeReuse : Bool
r136StrictFinitePlusTailMarginStillRequiredBeforeReuse = false

-- The typed terminal itself still contains the two genuine same-object physical
-- producers: boost covariance on the selected Local-C stress and E->L trace
-- continuation of that same object.  This is not recharged after the terminal
-- package is supplied.
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

    typedPinnedLocalCTerminalStillPhysical : Bool
    r109FiniteAnchorTailRechargedForStaticResponseReuse : Bool
    strictFiniteTailMarginRechargedForStaticResponseReuse : Bool
    r109FiniteAnchorTailStillPhysicalForIndependentSignRoute : Bool
    strictFiniteTailMarginStillPhysicalForIndependentSignRoute : Bool
    r136LorentzianContinuationStillPhysical : Bool
    ttProducerStillIndependent : Bool

canonicalPostNormalizationReuseFrontier : PostNormalizationReuseFrontier
canonicalPostNormalizationReuseFrontier =
  post-normalization-reuse-frontier
    true true false true false true true
    true false false true true true true

representationOnlyPromotionDebtRemainsAfterR136Reuse : Bool
representationOnlyPromotionDebtRemainsAfterR136Reuse = false

representationOnlyPromotionDebtRemainsAfterR136ReuseIsFalse :
  representationOnlyPromotionDebtRemainsAfterR136Reuse ≡ false
representationOnlyPromotionDebtRemainsAfterR136ReuseIsFalse = refl
