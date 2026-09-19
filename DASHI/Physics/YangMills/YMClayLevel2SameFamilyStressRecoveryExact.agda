{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2SameFamilyStressRecoveryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanLiteralSchwingerStressRecoveryRound126Exact as R126
import DASHI.Physics.YangMills.BalabanOSLiteralSchwingerWeldRound127Exact as R127
import DASHI.Physics.YangMills.BalabanSameFamilyOSStressRecoveryRound128Exact as R128
import DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact as R129
import DASHI.Physics.YangMills.BalabanCanonicalMetricStressLaneRound120Exact as R120
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as StressMarked
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- LEVEL-2 SAME-FAMILY STRESS RECOVERY FACTORIZATION
--
-- R129 already packages more than the previous closed-world audit credited.
-- Once an actual BalabanSectorQFTRecoveryExport is inhabited:
--
--   * the R127 OS -> literal-Schwinger weld is already inside R128;
--   * literal finite measures -> literal continuum measure is exported;
--   * literal Schwinger family membership in that measure is exported;
--   * the selected completed response is identified with the literal Clay
--     stress source derivative.
--
-- Therefore R127 is not an additional independent payment after R129 exists.
-- The remaining literal Clay stress/OPE debt lies downstream: promote the
-- recovered physical stress field into HasStressTensorAndOPE and identify the
-- actual OPE product/coefficient/remainder semantics.
------------------------------------------------------------------------

r129ExportsOSLiteralWeld :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation} →
  R129.BalabanSectorQFTRecoveryExport stressLane →
  R127.OSLiteralSchwingerWeld Y group
r129ExportsOSLiteralWeld export =
  R128.osWeld (R129.sameFamilyOSRecovery export)

r129ExportsLiteralContinuumLimit :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation} →
  (export : R129.BalabanSectorQFTRecoveryExport stressLane) →
  Top.IsContinuumLimitOf S group
    (Top.finiteMeasure Y group)
    (Top.continuumMeasure Y group)
r129ExportsLiteralContinuumLimit =
  R129.literalContinuumMeasureRecovery

r129ExportsLiteralSchwingerMembership :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation} →
  (export : R129.BalabanSectorQFTRecoveryExport stressLane) →
  Top.SchwingerBelongsToMeasure S
    (Top.continuumMeasure Y group)
    (Top.schwinger Y group)
r129ExportsLiteralSchwingerMembership =
  R129.literalSchwingerRecovery

r129ExportsLiteralStressDerivative :
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
      sources = R109.completedSources completion
      stressData = StressMarked.stressData sources
  in
  R114.cmp119CompletedResponse selected
  ≡ Marked.sourceDerivative stressData (Top.stressTensor Y group)
r129ExportsLiteralStressDerivative =
  R129.literalStressDerivativeRecovery


r129ExportsCompositeMarkedSourceData :
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
      sources = R109.completedSources completion
  in
  Marked.SameFamilyMarkedSourceData
    (R109.continuityScale completion)
    (R109.CompletedState completion)
    (R109.Composite completion)
r129ExportsCompositeMarkedSourceData {stressLane = stressLane} export =
  let selected = R120.coordinate (R123.stressLane stressLane)
      completion = R114.asMarkedCompletion selected (R114.coordinate selected)
      sources = R109.completedSources completion
  in
  StressMarked.compositeData sources

------------------------------------------------------------------------
-- Pareto bookkeeping.
------------------------------------------------------------------------

r127IndependentAfterR129Recovery : Bool
r127IndependentAfterR129Recovery = false

r127IndependentAfterR129RecoveryIsFalse :
  r127IndependentAfterR129Recovery ≡ false
r127IndependentAfterR129RecoveryIsFalse = refl

literalContinuumLimitIndependentAfterR129Recovery : Bool
literalContinuumLimitIndependentAfterR129Recovery = false

literalContinuumLimitIndependentAfterR129RecoveryIsFalse :
  literalContinuumLimitIndependentAfterR129Recovery ≡ false
literalContinuumLimitIndependentAfterR129RecoveryIsFalse = refl

literalSchwingerMembershipIndependentAfterR129Recovery : Bool
literalSchwingerMembershipIndependentAfterR129Recovery = false

literalSchwingerMembershipIndependentAfterR129RecoveryIsFalse :
  literalSchwingerMembershipIndependentAfterR129Recovery ≡ false
literalSchwingerMembershipIndependentAfterR129RecoveryIsFalse = refl

literalStressDerivativeIndependentAfterR129Recovery : Bool
literalStressDerivativeIndependentAfterR129Recovery = false

compositeMarkedSourceDataIndependentAfterR129Recovery : Bool
compositeMarkedSourceDataIndependentAfterR129Recovery = false

literalStressDerivativeIndependentAfterR129RecoveryIsFalse :
  literalStressDerivativeIndependentAfterR129Recovery ≡ false
literalStressDerivativeIndependentAfterR129RecoveryIsFalse = refl

compositeMarkedSourceDataIndependentAfterR129RecoveryIsFalse :
  compositeMarkedSourceDataIndependentAfterR129Recovery ≡ false
compositeMarkedSourceDataIndependentAfterR129RecoveryIsFalse = refl

r129SameFamilyRecoveryCompilerLevel : ProofLevel
r129SameFamilyRecoveryCompilerLevel = R129.balabanSectorQFTRecoveryExportCompilerLevel

physicalR129SameFamilyRecoveryLevel : ProofLevel
physicalR129SameFamilyRecoveryLevel = R129.literalBalabanSectorQFTRecoveryExportLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
