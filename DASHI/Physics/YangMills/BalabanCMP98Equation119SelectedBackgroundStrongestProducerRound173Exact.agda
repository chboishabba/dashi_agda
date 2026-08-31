{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundStrongestProducerRound173Exact where

------------------------------------------------------------------------
-- ROUND173 A1 BIDI: SELECTED BACKGROUND -> LITERAL EQ. (119)
--
-- Round174 now supplies a stronger same-object route for principal recognition:
-- the selected-background defect algebra itself recognizes the Round166 source
-- threshold once the single scalar comparison 1/24 <= selected chart radius is
-- supplied.  The older generic recognition entry points are retained for reuse,
-- while the strongest route below consumes the Round174 scalar receipt instead.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact as R159
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPrincipalChartRound166Exact as R166
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveLinkDefectRound168Exact as R168
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveLinkStrongestProducerRound169Exact as R169
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundBondWeldRound170Exact as R170
import DASHI.Physics.YangMills.BalabanCMP98SelectedChartThresholdRecognitionRound174Exact as R174

selectedBackgroundOneStepDerivative :
  ∀ {C n Value group CoarseField FineField Lie}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField} {FineField = FineField} {Lie = Lie} source)
    (recognition : R166.DefectRecognizedPrincipalChart
      source
      (R168.asLiteralRelativeDefectInputs
        source (R170.asPositiveLinkDefectInputs source weld))) →
  R159.UniformAdjointDifferentialCalculus
    (R126.Vector (R146.additive C)) →
  R126.OneStepAveragingDerivative (R146.additive C)
selectedBackgroundOneStepDerivative source weld recognition calculus =
  R169.positiveLinkOneStepDerivative
    source
    (R170.asPositiveLinkDefectInputs source weld)
    recognition
    calculus

selectedBackgroundMultiscaleDerivative :
  ∀ {C n Value group CoarseField FineField Lie}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField} {FineField = FineField} {Lie = Lie} source)
    (recognition : R166.DefectRecognizedPrincipalChart
      source
      (R168.asLiteralRelativeDefectInputs
        source (R170.asPositiveLinkDefectInputs source weld))) →
  R159.UniformAdjointDifferentialCalculus
    (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
selectedBackgroundMultiscaleDerivative source weld recognition calculus =
  R169.positiveLinkMultiscaleDerivative
    source
    (R170.asPositiveLinkDefectInputs source weld)
    recognition
    calculus

selectedBackgroundOneStepDerivativeFromThreshold :
  ∀ {C n Value group CoarseField FineField}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = R126.Vector (R146.additive C)}
      source) →
  R174.SelectedChartThresholdRecognition source weld →
  R159.UniformAdjointDifferentialCalculus
    (R126.Vector (R146.additive C)) →
  R126.OneStepAveragingDerivative (R146.additive C)
selectedBackgroundOneStepDerivativeFromThreshold source weld threshold calculus =
  selectedBackgroundOneStepDerivative
    source weld
    (R174.asDefectRecognizedPrincipalChart source weld threshold)
    calculus

selectedBackgroundMultiscaleDerivativeFromThreshold :
  ∀ {C n Value group CoarseField FineField}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField}
      {FineField = FineField}
      {Lie = R126.Vector (R146.additive C)}
      source) →
  R174.SelectedChartThresholdRecognition source weld →
  R159.UniformAdjointDifferentialCalculus
    (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
selectedBackgroundMultiscaleDerivativeFromThreshold source weld threshold calculus =
  selectedBackgroundMultiscaleDerivative
    source weld
    (R174.asDefectRecognizedPrincipalChart source weld threshold)
    calculus

cmp98Equation119SelectedBackgroundStrongestProducerRound173Level : ProofLevel
cmp98Equation119SelectedBackgroundStrongestProducerRound173Level = machineChecked

cmp98Equation119SelectedChartThresholdProducerRound173Level : ProofLevel
cmp98Equation119SelectedChartThresholdProducerRound173Level = machineChecked

-- Remaining strongest-route analytic normalization is now split cleanly:
--   (1) one scalar selected-chart threshold comparison (Round174), and
--   (2) the uniform exp/log differential + adjoint calculus (Round159).
-- No independent operator-defect principal-recognition object is required.
literalCMP98FinalAnalyticNormalizationRound173Level : ProofLevel
literalCMP98FinalAnalyticNormalizationRound173Level = conditional
