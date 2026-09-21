{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalPhysicalDecayRound451Exact where

------------------------------------------------------------------------
-- B / ROUND451: SELECTED CMP116 RESIDUAL WEIGHT -> PHYSICAL-TIME ENVELOPE.
--
-- R448 already proves
--
--   |selectedBoundary|
--     <= A_src * W(graphDist(leftMark,rightMark)).
--
-- The remaining B6 calibration should therefore be stated exactly at that
-- selected distance.  It is NOT necessary to identify W with halfPower or with
-- an exponential function definitionally.
--
-- Once a physical theorem proves
--
--   W(d_selected) <= physicalEnvelope(time),
--
-- nonnegativity of A_src and W compiles the final finite selected-boundary
-- physical decay bound.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; absℝ; _≤ℝ_; ≤ℝ-trans; mulMonotoneNonnegative)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YMSupportGraphDistance as Graph
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanCMP116CanonicalDomainRateSplitRound448Exact as R448

record CanonicalPhysicalDecayCalibration
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    (geometry : R448.CanonicalDomainSpecificRateSplit data)
    : Set₁ where
  field
    euclideanTime : Nat
    physicalEnvelope : Nat → ℝ

    -- Exact B6 physical calibration.  This may be discharged by an explicit
    -- exponential scale relation, a half-power comparison, or any stronger
    -- source-native estimate; downstream algebra observes only this inequality.
    selectedResidualBelowPhysicalEnvelope :
      R414.weight (R448.sourceDecay geometry)
        (Graph.ymGraphDist (R444.leftMark data) (R444.rightMark data))
      ≤ℝ
      physicalEnvelope euclideanTime

open CanonicalPhysicalDecayCalibration public

selectedBoundaryBelowPhysicalEnvelope :
  ∀ {Measure TestObservable dataSet extension base data}
    {geometry : R448.CanonicalDomainSpecificRateSplit data}
    (calibration : CanonicalPhysicalDecayCalibration geometry) →
  absℝ (R444.selectedBoundaryIntegrand data)
  ≤ℝ
  R448.sourceAmplitude geometry *ℝ
    physicalEnvelope calibration (euclideanTime calibration)
selectedBoundaryBelowPhysicalEnvelope {data = data} {geometry = geometry}
    calibration =
  let
    selectedDistance =
      Graph.ymGraphDist (R444.leftMark data) (R444.rightMark data)

    sourceBound =
      R448.selectedBoundaryBelowSourceDecay data geometry

    scaledCalibration =
      mulMonotoneNonnegative
        (R448.sourceAmplitudeNonnegative geometry)
        DASHI.Foundations.RealAnalysisAxioms.≤ℝ-refl
        (R414.weightNonnegative (R448.sourceDecay geometry) selectedDistance)
        (selectedResidualBelowPhysicalEnvelope calibration)
  in
  ≤ℝ-trans sourceBound scaledCalibration

round451PhysicalDecayCompilerLevel : ProofLevel
round451PhysicalDecayCompilerLevel = machineChecked

-- B6 is exactly the selected residual-weight -> physical-time envelope theorem.
literalRound451ResidualToPhysicalEnvelopeLevel : ProofLevel
literalRound451ResidualToPhysicalEnvelopeLevel = conditional
