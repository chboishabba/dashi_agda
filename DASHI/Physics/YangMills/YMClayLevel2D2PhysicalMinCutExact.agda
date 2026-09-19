{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2D2PhysicalMinCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCompositeOperatorRGParallelTransportExact as Transport
import DASHI.Physics.YangMills.YMClayLevel2CompositeOperatorCoefficientWeldExact as Native
import DASHI.Physics.YangMills.YMClayLevel2LiteralOPECoefficientScaleAttachmentExact as Literal
import DASHI.Physics.YangMills.BalabanOPECoefficientRGRecurrenceUniquenessExact as OPE

------------------------------------------------------------------------
-- LEVEL-2 D2 PHYSICAL MIN-CUT
--
-- D2 is now split at the actual repo-native interfaces:
--
--   D2a  instantiate CompositeRGParallelTransport on the physical composite
--        operator carrier;
--
--   D2b  supply physical/reference operator-coefficient trajectories using that
--        SAME one-step mixing map and SAME UV normalization;
--
--   D2c  attach the literal position-dependent Clay OPE coefficient to the
--        projected physical operator coordinate at a certified short-distance
--        RG depth.
--
-- Everything after those attachments is compiler-owned:
--
--   D2a+D2b -> CoefficientRGRecurrence
--   recurrence uniqueness -> all-depth physical/reference equality
--   D2c -> literal Clay coefficient = projected AF/reference coefficient
--          at the selected physical short-distance depth.
------------------------------------------------------------------------

d2aPhysicalCompositeOperatorTransportLevel : ProofLevel
d2aPhysicalCompositeOperatorTransportLevel =
  Transport.physicalYMCompositeMixingLevel

d2bSameTransportCoefficientTrajectoryLevel : ProofLevel
d2bSameTransportCoefficientTrajectoryLevel = conditional

d2cLiteralPositionDepthAttachmentLevel : ProofLevel
d2cLiteralPositionDepthAttachmentLevel =
  Literal.physicalPositionDepthAttachmentLevel

compositeOperatorToRecurrenceCompilerLevel : ProofLevel
compositeOperatorToRecurrenceCompilerLevel =
  Native.compositeOperatorToOPERecurrenceCompilerLevel

allDepthCoefficientCompilerLevel : ProofLevel
allDepthCoefficientCompilerLevel =
  OPE.coefficientRGRecurrenceUniquenessLevel

literalSelectedDepthCoefficientCompilerLevel : ProofLevel
literalSelectedDepthCoefficientCompilerLevel =
  Literal.scaleAttachmentCompilerLevel

secondMixingMapResearchProblem : Bool
secondMixingMapResearchProblem = false

secondMixingMapResearchProblemIsFalse :
  secondMixingMapResearchProblem ≡ false
secondMixingMapResearchProblemIsFalse = refl

literalClayCoefficientCanBeTreatedAsConstantNatFamily : Bool
literalClayCoefficientCanBeTreatedAsConstantNatFamily = false

literalClayCoefficientCanBeTreatedAsConstantNatFamilyIsFalse :
  literalClayCoefficientCanBeTreatedAsConstantNatFamily ≡ false
literalClayCoefficientCanBeTreatedAsConstantNatFamilyIsFalse = refl

positionDepthSemanticsIsIndependentPhysicalAttachment : Bool
positionDepthSemanticsIsIndependentPhysicalAttachment = true

positionDepthSemanticsIsIndependentPhysicalAttachmentIsTrue :
  positionDepthSemanticsIsIndependentPhysicalAttachment ≡ true
positionDepthSemanticsIsIndependentPhysicalAttachmentIsTrue = refl

newGlobalAFTheoremRequired : Bool
newGlobalAFTheoremRequired = false

newGlobalAFTheoremRequiredIsFalse :
  newGlobalAFTheoremRequired ≡ false
newGlobalAFTheoremRequiredIsFalse = refl

newAllDepthCoefficientProofRequired : Bool
newAllDepthCoefficientProofRequired = false

newAllDepthCoefficientProofRequiredIsFalse :
  newAllDepthCoefficientProofRequired ≡ false
newAllDepthCoefficientProofRequiredIsFalse = refl

d2PhysicalMinCutLevel : ProofLevel
d2PhysicalMinCutLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
