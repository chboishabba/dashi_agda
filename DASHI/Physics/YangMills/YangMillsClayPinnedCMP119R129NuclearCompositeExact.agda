{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119R129NuclearCompositeExact where

------------------------------------------------------------------------
-- C / R129 EXPORT -> ACTUAL NUCLEAR-CONTINUOUS COMPLETED COMPOSITE
--
-- This is a genuine downstream inhabitant, not a new interface:
--
--   R129 same-family recovery export
--      -> SameFamilyMarkedSourceData
--      -> SameFamilyNuclearCompositeField.
--
-- Thus nuclear completion/continuity of the base completed composite is already
-- theorem output once R129 is inhabited.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact as R129
import DASHI.Physics.YangMills.YMClayLevel2SameFamilyStressRecoveryExact as Recovery
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

r129CompletedCompositeNuclearField :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    (export : R129.BalabanSectorQFTRecoveryExport stressLane) →
  Marked.SameFamilyNuclearCompositeField
    (Recovery.r129ExportsCompositeMarkedSourceData export)
r129CompletedCompositeNuclearField export =
  Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
    (Recovery.r129ExportsCompositeMarkedSourceData export)

r129CompletedCompositeIsSameProjection :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    (export : R129.BalabanSectorQFTRecoveryExport stressLane) →
  Marked.continuumComposite (r129CompletedCompositeNuclearField export)
  ≡
  Marked.compositeProjection
    (Recovery.r129ExportsCompositeMarkedSourceData export)
    (Marked.completedState
      (Recovery.r129ExportsCompositeMarkedSourceData export))
r129CompletedCompositeIsSameProjection export =
  Marked.continuumCompositeIsSameProjection
    (r129CompletedCompositeNuclearField export)

r129CompletedCompositeNuclearCompilerLevel : ProofLevel
r129CompletedCompositeNuclearCompilerLevel =
  Marked.markedSourceToNuclearCompositeFieldCompilerLevel

-- Remaining C1a work is no longer nuclear completion of this base composite.
-- It is the physical selection of the required curvature-polynomial family and
-- gauge/local semantics on the same completed R129 carrier.
literalCurvatureFamilyProjectionFromR129Level : ProofLevel
literalCurvatureFamilyProjectionFromR129Level = conditional
