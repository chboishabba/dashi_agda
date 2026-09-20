{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116Round406SupportGraphPreferredR415Round419Exact where

------------------------------------------------------------------------
-- ROUND419 / CURRENT LITERAL B SOURCE CUT
--
-- Compose the strongest existing source-native route:
--
--   R406 literal selected CMP116 decomposition
--     + exact R406 -> R410 replay
--     + concrete support-graph geometry
--       -> preferred R415 selected source decay.
--
-- Two historical leaves disappear on this route:
--
--   * no independent marked-charging theorem:
--       R406's already-proved positive common-Y majorant sum is transported
--       directly to the canonical R410 majorant;
--
--   * no independent selected-distance theorem:
--       support-graph minimality + tree-edge bound compile it once the selected
--       two-mark membership/metric attachments are supplied.
--
-- Thus the physical frontier is reduced to:
--
--   B1 exact literal R406 term = exact R410 term/majorant;
--   B4 selected surviving-term support membership + metric attachment;
--   B6 per-domain shell <= A_Y W(d_Y);
--   B7 sum_Y A_Y <= A_src.
--
-- Downstream source-envelope / real physical-rate identification remains a
-- separate same-object application seam and is intentionally not hidden here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP116Round406To415Exact as Replay
import DASHI.Physics.YangMills.BalabanCMP116Round406SupportGraphGeometryExact as GraphGeometry
import DASHI.Physics.YangMills.BalabanCMP116PreferredR415SourceExact as Preferred
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414

record LiteralRound406SupportGraphBSource
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    : Set₁ where
  field
    replay : Replay.Round406ExactR410Replay application

    supportGraphGeometry :
      GraphGeometry.Round406SupportGraphGeometry
        {Measure = Measure}
        {TestObservable = TestObservable}
        {dataSet = dataSet}
        {extension = extension}
        {base = base}
        application

open LiteralRound406SupportGraphBSource public

compilePreferredR415 :
  ∀ {Measure TestObservable dataSet extension base}
    {application : R406.SelectedCMP116TermwiseLocalization base} →
  LiteralRound406SupportGraphBSource
    {Measure = Measure}
    {TestObservable = TestObservable}
    {dataSet = dataSet}
    {extension = extension}
    {base = base}
    application →
  Preferred.PreferredR415Source
    (R406.Domain application)
    (R406.Term application)
    (R406.Operator application)
compilePreferredR415 {application = application} source =
  GraphGeometry.compilePreferredFromSupportGraph
    application
    (replay source)
    (supportGraphGeometry source)

selectedBoundaryBelowConnectingDecay :
  ∀ {Measure TestObservable dataSet extension base}
    {application : R406.SelectedCMP116TermwiseLocalization base}
    (source :
      LiteralRound406SupportGraphBSource
        {Measure = Measure}
        {TestObservable = TestObservable}
        {dataSet = dataSet}
        {extension = extension}
        {base = base}
        application) →
  absℝ (R406.selectedBoundaryIntegrand application)
  ≤ℝ
  GraphGeometry.sourceAmplitude (supportGraphGeometry source)
    *ℝ
    R414.weight
      (GraphGeometry.decay (supportGraphGeometry source))
      (R411.selectedConnectingDistance
        (GraphGeometry.geometry
          (GraphGeometry.asRound406To415Geometry
            application (supportGraphGeometry source))))
selectedBoundaryBelowConnectingDecay {application = application} source =
  Preferred.preferredR415SelectedBoundaryDecay
    (compilePreferredR415 source)

------------------------------------------------------------------------
-- Exact frontier accounting.
------------------------------------------------------------------------

round419SeparateMarkedChargingLeafRequired : Bool
round419SeparateMarkedChargingLeafRequired = false

round419SeparateMarkedChargingLeafRequiredIsFalse :
  round419SeparateMarkedChargingLeafRequired ≡ false
round419SeparateMarkedChargingLeafRequiredIsFalse = refl

round419SeparateFixedYSummabilityLeafRequired : Bool
round419SeparateFixedYSummabilityLeafRequired = false

round419SeparateFixedYSummabilityLeafRequiredIsFalse :
  round419SeparateFixedYSummabilityLeafRequired ≡ false
round419SeparateFixedYSummabilityLeafRequiredIsFalse = refl

round419SeparateSelectedDistanceInequalityLeafRequired : Bool
round419SeparateSelectedDistanceInequalityLeafRequired = false

round419SeparateSelectedDistanceInequalityLeafRequiredIsFalse :
  round419SeparateSelectedDistanceInequalityLeafRequired ≡ false
round419SeparateSelectedDistanceInequalityLeafRequiredIsFalse = refl

round419PreferredR415CompilerLevel : ProofLevel
round419PreferredR415CompilerLevel = machineChecked

-- Genuine remaining source mathematics on this route.
literalRound419ExactR406R410ReplayLevel : ProofLevel
literalRound419ExactR406R410ReplayLevel =
  Replay.literalRound406ExactR410ReplayLevel

literalRound419SupportGraphAmplitudeLevel : ProofLevel
literalRound419SupportGraphAmplitudeLevel =
  GraphGeometry.literalRound406SupportGraphAndAmplitudeLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
