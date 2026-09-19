{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayF1PhysicalMinCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116R281SelectedSourceUpperRound343Exact as R343
import DASHI.Physics.YangMills.BalabanCMP116SharedMarkedDirectCalibrationRound344Exact as R344
import DASHI.Physics.YangMills.BalabanCMP116SharedMarkedAmplitudeDirectRound346Exact as R346
import DASHI.Physics.YangMills.YMClayF1WilsonR295SameObjectWeldExact as WilsonR295

------------------------------------------------------------------------
-- F1 PHYSICAL MIN-CUT RECONCILIATION
--
-- Full R339 source-magnitude equality is stronger than the terminal mass-gap
-- consumer requires. R343 explicitly weakens that equality to the one-sided
-- selected-response upper; R344/R346 continue on the actual shared-marked
-- physical source carrier.
--
-- Primitive physical cut:
--   A. selected CMP116 localization on the actual canonical/source carrier;
--   B. physical R315 Wilson-cylinder presentation on the SAME R295/T5 carrier;
--   C. rooted/source envelope <= c_k ||psi||^2 on the physical L2 carrier;
--   D. Delta*a_k <= 1-c_k on the same beta-history trajectory.
------------------------------------------------------------------------

record PhysicalWilsonT5DenseL2Weld : Set₁ where
  field
    ActualSelectedCMP116Localization : Set
    actualSelectedCMP116Localization :
      ActualSelectedCMP116Localization

    -- Compatibility slot for callers of the first reconciliation tranche.
    -- The canonical typed owner is now YMClayF1WilsonR295SameObjectWeldExact:
    -- once its R315 presentation is inhabited, no additional carrier equality
    -- theorem is required.
    LiteralWilsonEqualsSelectedT5Observable : Set
    literalWilsonEqualsSelectedT5Observable :
      LiteralWilsonEqualsSelectedT5Observable

    DensePhysicalVacuumComplement : Set
    densePhysicalVacuumComplement :
      DensePhysicalVacuumComplement

    RootedSourceEnvelopeL2Calibration : Set
    rootedSourceEnvelopeL2Calibration :
      RootedSourceEnvelopeL2Calibration

    BetaHistoryTrajectoryGapCalibration : Set
    betaHistoryTrajectoryGapCalibration :
      BetaHistoryTrajectoryGapCalibration

open PhysicalWilsonT5DenseL2Weld public

fullR339MagnitudeEqualityPrimitive : Bool
fullR339MagnitudeEqualityPrimitive = false

fullR339MagnitudeEqualityPrimitiveIsFalse :
  fullR339MagnitudeEqualityPrimitive ≡ false
fullR339MagnitudeEqualityPrimitiveIsFalse = refl

r343OneSidedSelectedUpperIsPreferredConsumerShape : Bool
r343OneSidedSelectedUpperIsPreferredConsumerShape = true

r343OneSidedSelectedUpperIsPreferredConsumerShapeIsTrue :
  r343OneSidedSelectedUpperIsPreferredConsumerShape ≡ true
r343OneSidedSelectedUpperIsPreferredConsumerShapeIsTrue = refl

r343ConfirmsMagnitudeEqualityNotPrimitive : Bool
r343ConfirmsMagnitudeEqualityNotPrimitive =
  R343.sourceMagnitudeEqualityPrimitiveForMassGapConsumer

r344R346SharedMarkedRouteAvailable : Bool
r344R346SharedMarkedRouteAvailable = true

r344R346SharedMarkedRouteAvailableIsTrue :
  r344R346SharedMarkedRouteAvailable ≡ true
r344R346SharedMarkedRouteAvailableIsTrue = refl


------------------------------------------------------------------------
-- F1-B reduction: the selected Wilson/R295 carrier equality is not another
-- primitive theorem.  R315 is already typed over the R295-derived exact T5
-- carrier and explicitly welds Wilson products/multiplication to the T5
-- observable algebra.  Only the physical R315 presentation inhabitant remains.
------------------------------------------------------------------------

independentWilsonR295CarrierEqualityPrimitive : Bool
independentWilsonR295CarrierEqualityPrimitive =
  WilsonR295.independentWilsonToR295CarrierEqualityRequired

f1BPhysicalResidueIsR315Presentation : Bool
f1BPhysicalResidueIsR315Presentation =
  WilsonR295.f1BPhysicalResidueIsR315Presentation

f1BPhysicalWilsonPresentationLevel : ProofLevel
f1BPhysicalWilsonPresentationLevel =
  WilsonR295.f1BPhysicalWilsonPresentationLevel

weakestSelectedLocalizationLevel : ProofLevel
weakestSelectedLocalizationLevel =
  R346.round346LiteralSelectedLocalizationLevel

physicalWilsonT5DenseL2WeldLevel : ProofLevel
physicalWilsonT5DenseL2WeldLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
