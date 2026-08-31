{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundStrongestProducerRound173Exact where

------------------------------------------------------------------------
-- ROUND173 A1 BIDI: SELECTED BACKGROUND -> LITERAL EQ. (119)
--
-- This is the strongest current consumer.  It composes the selected
-- variational-background same-object weld (R170), theorem-generated contour
-- length (R172), positive-to-oriented link reduction (R168), literal 74-link
-- relative defect (R164--R165), principal-chart admission (R166), and one
-- uniform exp/log differential calculus (R159).
--
-- There is no positive-link defect receipt at this API boundary.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact as R159
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPrincipalChartRound166Exact as R166
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveLinkStrongestProducerRound169Exact as R169
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundBondWeldRound170Exact as R170

selectedBackgroundOneStepDerivative :
  ∀ {C n Value group CoarseField FineField Lie}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField} {FineField = FineField} {Lie = Lie} source)
    (recognition : R166.DefectRecognizedPrincipalChart
      source
      (DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveLinkDefectRound168Exact.asLiteralRelativeDefectInputs
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
      (DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveLinkDefectRound168Exact.asLiteralRelativeDefectInputs
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

cmp98Equation119SelectedBackgroundStrongestProducerRound173Level : ProofLevel
cmp98Equation119SelectedBackgroundStrongestProducerRound173Level = machineChecked

-- Remaining analytic/source surfaces at the strongest boundary are now:
--   * concrete selected variational bridge / operator-kernel instantiation;
--   * the standard defect<=1/24 principal-image recognition;
--   * the single CMP98 exp/log/dexp/adjoint coordinate normalization.
-- Positive-link smallness and contour length are not independent inputs.
literalCMP98FinalAnalyticNormalizationRound173Level : ProofLevel
literalCMP98FinalAnalyticNormalizationRound173Level = conditional
