{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98SelectedChartThresholdRecognitionRound174Exact where

------------------------------------------------------------------------
-- ROUND174 A1 BIDI: REUSE THE SELECTED-BACKGROUND PRINCIPAL CUT DIRECTLY
--
-- Round170 already identifies the literal Eq. (119) telescope defect with the
-- defect algebra carried by the selected variational-background chart.  That
-- same chart already owns `defectBelowRadiusImpliesAdmissible` and identifies
-- its admissibility predicate with the selected principal image.
--
-- Therefore Round166 does not need an independent operator-norm -> principal-
-- image recognition theorem.  The only remaining scalar comparison is
--
--     1/24 <= selected chart radius.
--
-- Once supplied, the exact selected defect algebra recognizes every value under
-- the Round166 source threshold.  This keeps the path telescope and principal
-- chart on one defect convention rather than switching analytic norms at the
-- final consumer.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (_≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralRelativeDefectRound164Exact as R164
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPrincipalChartRound166Exact as R166
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveLinkDefectRound168Exact as R168
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundBondWeldRound170Exact as R170

record SelectedChartThresholdRecognition
    {C n Value group CoarseField FineField}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = R126.Vector (R146.additive C)}
      source) : Set where
  field
    sourceThresholdBelowSelectedChartRadius :
      Chart.sourceDefectThreshold ≤
      Path.chartRadius (Selected.cutData (R170.bridge weld))

open SelectedChartThresholdRecognition public

selectedDefectBelowThreshold :
  ∀ {C n Value group CoarseField FineField}
    {source : R158.CanonicalL13Equation119Source C n Value group}
    {weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = R126.Vector (R146.additive C)}
      source} →
  ∀ value →
  Telescope.defect
    (R164.kernel
      (R168.asLiteralRelativeDefectInputs source
        (R170.asPositiveLinkDefectInputs source weld))) value
    ≤ Chart.sourceDefectThreshold →
  Path.defect (Selected.defectAlgebra (R170.bridge weld)) value
    ≤ Chart.sourceDefectThreshold
selectedDefectBelowThreshold {weld = weld} value defectSmall =
  subst
    (λ lower → lower ≤ Chart.sourceDefectThreshold)
    (R170.kernelDefectIsSelectedDefect weld value)
    defectSmall

selectedDefectBelowSelectedChartRadius :
  ∀ {C n Value group CoarseField FineField}
    {source : R158.CanonicalL13Equation119Source C n Value group}
    {weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = R126.Vector (R146.additive C)}
      source} →
  SelectedChartThresholdRecognition source weld →
  ∀ value →
  Telescope.defect
    (R164.kernel
      (R168.asLiteralRelativeDefectInputs source
        (R170.asPositiveLinkDefectInputs source weld))) value
    ≤ Chart.sourceDefectThreshold →
  Scale.LessEqual
    (Path.scale (Selected.defectAlgebra (R170.bridge weld)))
    (Path.defect (Selected.defectAlgebra (R170.bridge weld)) value)
    (Path.chartRadius (Selected.cutData (R170.bridge weld)))
selectedDefectBelowSelectedChartRadius {weld = weld} recognition value defectSmall =
  let
    bridge = R170.bridge weld
    selectedAlgebra = Selected.defectAlgebra bridge
    selectedRational :
      Path.defect selectedAlgebra value ≤ Chart.sourceDefectThreshold
    selectedRational = selectedDefectBelowThreshold value defectSmall

    selectedScaleThreshold :
      Scale.LessEqual (Path.scale selectedAlgebra)
        (Path.defect selectedAlgebra value) Chart.sourceDefectThreshold
    selectedScaleThreshold =
      subst
        (λ relation → relation
          (Path.defect selectedAlgebra value) Chart.sourceDefectThreshold)
        (sym (R170.chartOrderIsRationalOrder weld))
        selectedRational

    thresholdScaleRadius :
      Scale.LessEqual (Path.scale selectedAlgebra)
        Chart.sourceDefectThreshold
        (Path.chartRadius (Selected.cutData bridge))
    thresholdScaleRadius =
      subst
        (λ relation → relation Chart.sourceDefectThreshold
          (Path.chartRadius (Selected.cutData bridge)))
        (sym (R170.chartOrderIsRationalOrder weld))
        (sourceThresholdBelowSelectedChartRadius recognition)
  in
  Scale.transitive (Path.scale selectedAlgebra)
    selectedScaleThreshold thresholdScaleRadius

selectedThresholdImpliesPrincipalImage :
  ∀ {C n Value group CoarseField FineField}
    {source : R158.CanonicalL13Equation119Source C n Value group}
    {weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = R126.Vector (R146.additive C)}
      source} →
  (recognition : SelectedChartThresholdRecognition source weld) →
  ∀ value →
  Telescope.defect
    (R164.kernel
      (R168.asLiteralRelativeDefectInputs source
        (R170.asPositiveLinkDefectInputs source weld))) value
    ≤ Chart.sourceDefectThreshold →
  Log.InPrincipalImage (Selected.principalChart (R170.bridge weld)) value
selectedThresholdImpliesPrincipalImage {weld = weld} recognition value defectSmall =
  let
    bridge = R170.bridge weld
    cut = Selected.cutData bridge

    selectedBound =
      selectedDefectBelowSelectedChartRadius recognition value defectSmall

    cutBound :
      Scale.LessEqual (Path.scale (Path.defectAlgebra cut))
        (Path.defect (Path.defectAlgebra cut) value)
        (Path.chartRadius cut)
    cutBound =
      subst
        (λ algebra →
          Scale.LessEqual (Path.scale algebra)
            (Path.defect algebra value) (Path.chartRadius cut))
        (sym (Selected.sameDefectAlgebra bridge))
        selectedBound

    admitted : Path.PrincipalLogAdmissible cut value
    admitted = Path.defectBelowRadiusImpliesAdmissible cut value cutBound
  in
  subst
    (λ predicate → predicate value)
    (Selected.admissibleIsPrincipalImage bridge)
    admitted

asDefectRecognizedPrincipalChart :
  ∀ {C n Value group CoarseField FineField}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = R126.Vector (R146.additive C)}
      source) →
  SelectedChartThresholdRecognition source weld →
  R166.DefectRecognizedPrincipalChart
    source
    (R168.asLiteralRelativeDefectInputs source
      (R170.asPositiveLinkDefectInputs source weld))
asDefectRecognizedPrincipalChart source weld recognition = record
  { R166.DefectRecognizedPrincipalChart.chart =
      Selected.principalChart (R170.bridge weld)
  ; R166.DefectRecognizedPrincipalChart.defectBelowSourceThresholdImpliesPrincipalImage =
      selectedThresholdImpliesPrincipalImage recognition
  }

cmp98SelectedChartThresholdRecognitionRound174Level : ProofLevel
cmp98SelectedChartThresholdRecognitionRound174Level = machineChecked

-- The principal-recognition seam is now one scalar comparison on the SAME
-- selected-background chart already used by the positive-bond weld.
literalCMP98SourceThresholdBelowSelectedChartRadiusRound174Level : ProofLevel
literalCMP98SourceThresholdBelowSelectedChartRadiusRound174Level = conditional
