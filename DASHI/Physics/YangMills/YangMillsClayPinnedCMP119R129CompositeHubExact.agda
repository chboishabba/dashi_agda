{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119R129CompositeHubExact where

------------------------------------------------------------------------
-- C / R129 SAME-FAMILY RECOVERY IS THE HUB FOR COMPOSITE + STRESS
--
-- This owner is deliberately thin.  R129 already exports the same-family
-- continuum/Schwinger/stress/composite facts; downstream pinned C code should
-- consume those exports rather than ask for duplicate recovery witnesses.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact as R129
import DASHI.Physics.YangMills.YMClayLevel2SameFamilyStressRecoveryExact as Recovery
import DASHI.Physics.YangMills.BalabanCanonicalMetricStressLaneRound120Exact as R120
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

r129LiteralContinuumLimit =
  Recovery.r129ExportsLiteralContinuumLimit

r129LiteralSchwingerMembership =
  Recovery.r129ExportsLiteralSchwingerMembership

r129OSLiteralWeld =
  Recovery.r129ExportsOSLiteralWeld

r129LiteralStressDerivative =
  Recovery.r129ExportsLiteralStressDerivative

r129CompositeMarkedSource :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    (export : R129.BalabanSectorQFTRecoveryExport stressLane) →
  let selected = R120.coordinate (R123.stressLane stressLane)
      completion = R114.asMarkedCompletion selected (R114.coordinate selected)
  in
  Marked.SameFamilyMarkedSourceData
    (R109.continuityScale completion)
    (R109.CompletedState completion)
    (R109.Composite completion)
r129CompositeMarkedSource =
  Recovery.r129ExportsCompositeMarkedSourceData

r129SameFamilyRecoveryHubCompilerLevel : ProofLevel
r129SameFamilyRecoveryHubCompilerLevel =
  Recovery.r129SameFamilyRecoveryCompilerLevel

-- No new physical payment is introduced here.  The source leaves remain those
-- already required to inhabit R129 itself and the downstream curvature/stress
-- semantic projections.
literalR129SameFamilyRecoveryLevel : ProofLevel
literalR129SameFamilyRecoveryLevel =
  Recovery.physicalR129SameFamilyRecoveryLevel
