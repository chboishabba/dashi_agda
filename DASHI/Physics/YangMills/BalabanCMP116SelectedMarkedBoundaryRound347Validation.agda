{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedBoundaryRound347Validation where

------------------------------------------------------------------------
-- RED-first validation root for the R346 -> R347 Pareto recut.
--
-- This root intentionally targets only the least-privilege boundary below
-- R346's literal selected localization field:
--
--   selected physical J-attachment
--   + selected CMP116 marked boundary/substitution comparison
--   -> already-owned generic Cauchy/Hessian coefficient lift
--   -> R346 L_marked.
--
-- It must not reintroduce:
--   * R343 sourceEnvelope -> clusteringEnvelope calibration;
--   * rootedShell <= markedAnalyticShell;
--   * equality with the older hessianInfluenceShell;
--   * C_H <= 1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedBoundaryFrontierRound347Exact as R347

genericBoundaryToCauchyLiftLevel : ProofLevel
genericBoundaryToCauchyLiftLevel = R347.genericBoundaryToCauchyLiftLevel

selectedMarkedBoundarySubstitutionLevel : ProofLevel
selectedMarkedBoundarySubstitutionLevel = R347.selectedMarkedBoundarySubstitutionLevel

selectedJPhysicalCoordinateAttachmentLevel : ProofLevel
selectedJPhysicalCoordinateAttachmentLevel = R347.selectedJPhysicalCoordinateAttachmentLevel

selectedDistanceTimeLevel : ProofLevel
selectedDistanceTimeLevel = R347.selectedDistanceTimeLevel

rootedShellReverseComparisonRequired : Bool
rootedShellReverseComparisonRequired = R347.rootedShellReverseComparisonRequired

rootedShellReverseComparisonRequiredIsFalse : rootedShellReverseComparisonRequired ≡ false
rootedShellReverseComparisonRequiredIsFalse = R347.rootedShellReverseComparisonRequiredIsFalse

hessianInfluenceShellEqualityRequired : Bool
hessianInfluenceShellEqualityRequired = R347.hessianInfluenceShellEqualityRequired

hessianInfluenceShellEqualityRequiredIsFalse : hessianInfluenceShellEqualityRequired ≡ false
hessianInfluenceShellEqualityRequiredIsFalse = R347.hessianInfluenceShellEqualityRequiredIsFalse

r343SourceEnvelopeCalibrationStillPrimitive : Bool
r343SourceEnvelopeCalibrationStillPrimitive = R347.r343SourceEnvelopeCalibrationStillPrimitive

r343SourceEnvelopeCalibrationStillPrimitiveIsFalse :
  r343SourceEnvelopeCalibrationStillPrimitive ≡ false
r343SourceEnvelopeCalibrationStillPrimitiveIsFalse =
  R347.r343SourceEnvelopeCalibrationStillPrimitiveIsFalse

round347ClayPromotion : Bool
round347ClayPromotion = R347.clayPromotion

round347ClayPromotionIsFalse : round347ClayPromotion ≡ false
round347ClayPromotionIsFalse = R347.clayPromotionIsFalse
