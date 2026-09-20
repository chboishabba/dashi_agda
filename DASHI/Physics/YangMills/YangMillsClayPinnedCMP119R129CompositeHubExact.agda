{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119R129CompositeHubExact where

------------------------------------------------------------------------
-- C / R129 SAME-FAMILY RECOVERY IS THE HUB FOR COMPOSITE + STRESS
--
-- R129 already exports:
--   * literal finite family -> literal continuum measure,
--   * literal Schwinger membership,
--   * source OS -> literal Schwinger weld,
--   * completed stress derivative,
--   * completed composite marked-source data.
--
-- This module prevents those facts from being re-requested by the pinned
-- curvature/stress consumers.  The remaining physical input is only how each
-- desired curvature polynomial selects a composite projection from the SAME
-- completed R129 source state.
------------------------------------------------------------------------

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
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119MarkedCurvatureCompositeExact as Curvature

record R129CurvatureCompositeHub
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    (export : R129.BalabanSectorQFTRecoveryExport stressLane)
    (CurvaturePolynomial Position : Set)
    : Set₂ where
  field
    -- All selected curvature composites live on the same completed source
    -- topology/state exported by R129.
    markedSourceFor :
      CurvaturePolynomial →
      Marked.SameFamilyMarkedSourceData
        _
        _
        _

    GaugeInvariant :
      _ → Set

    LocalAt :
      _ → Position → Set

    completedGaugeInvariant :
      ∀ polynomial →
      GaugeInvariant
        (Marked.continuumComposite
          (Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
            (markedSourceFor polynomial)))

    completedLocal :
      ∀ polynomial position →
      LocalAt
        (Marked.continuumComposite
          (Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
            (markedSourceFor polynomial)))
        position

    -- Same completed carrier: every selected curvature source is a projection
    -- of the R129 exported completed marked source, not a second continuum
    -- family.  This is the only family-selection seam retained here.
    selectedSourceIsR129Projection : ∀ polynomial → Set

open R129CurvatureCompositeHub public

-- R129's stress/composite source is available without an additional recovery
-- premise.  This theorem is intentionally exposed so downstream code can use
-- it as the canonical donor.
r129BaseCompositeMarkedSource :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain
      representation stressLane}
    (export : R129.BalabanSectorQFTRecoveryExport
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane) →
  _
r129BaseCompositeMarkedSource export =
  Recovery.r129ExportsCompositeMarkedSourceData export

r129CompositeHubCompilerLevel : ProofLevel
r129CompositeHubCompilerLevel =
  Recovery.r129SameFamilyRecoveryCompilerLevel

literalR129CurvatureProjectionFamilyLevel : ProofLevel
literalR129CurvatureProjectionFamilyLevel = conditional
