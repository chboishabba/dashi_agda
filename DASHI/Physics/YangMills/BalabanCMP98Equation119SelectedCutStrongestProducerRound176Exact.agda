{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedCutStrongestProducerRound176Exact where

------------------------------------------------------------------------
-- ROUND176 A1 BIDI: SELECTED BACKGROUND + EXISTING CUT -> EQ. (119)
--
-- R175 derives R166 principal-image recognition from the cut/chart already
-- stored in the selected-background bridge.  Consequently the strongest
-- Eq. (119) API no longer accepts a recognition theorem at all.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact as R159
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveLinkDefectRound168Exact as R168
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundBondWeldRound170Exact as R170
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundStrongestProducerRound173Exact as R173
import DASHI.Physics.YangMills.BalabanCMP98Equation119ExistingCutRecognitionRound174Exact as R174
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedExistingCutRound175Exact as R175

selectedCutOneStepDerivative :
  ∀ {C n Value group CoarseField FineField Lie}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField} {FineField = FineField} {Lie = Lie} source)
    (cutInputs : R175.SelectedExistingCutInputs source weld) →
  R159.UniformAdjointDifferentialCalculus
    (R126.Vector (R146.additive C)) →
  R126.OneStepAveragingDerivative (R146.additive C)
selectedCutOneStepDerivative source weld cutInputs calculus =
  R173.selectedBackgroundOneStepDerivative
    source weld
    (R174.asRound166Recognition
      source
      (R168.asLiteralRelativeDefectInputs
        source (R170.asPositiveLinkDefectInputs source weld))
      (R175.asExistingCutRecognition source weld cutInputs))
    calculus

selectedCutMultiscaleDerivative :
  ∀ {C n Value group CoarseField FineField Lie}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (weld : R170.SelectedBackgroundBondWeld
      {CoarseField = CoarseField} {FineField = FineField} {Lie = Lie} source)
    (cutInputs : R175.SelectedExistingCutInputs source weld) →
  R159.UniformAdjointDifferentialCalculus
    (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
selectedCutMultiscaleDerivative source weld cutInputs calculus =
  R173.selectedBackgroundMultiscaleDerivative
    source weld
    (R174.asRound166Recognition
      source
      (R168.asLiteralRelativeDefectInputs
        source (R170.asPositiveLinkDefectInputs source weld))
      (R175.asExistingCutRecognition source weld cutInputs))
    calculus

cmp98Equation119SelectedCutStrongestProducerRound176Level : ProofLevel
cmp98Equation119SelectedCutStrongestProducerRound176Level = machineChecked

-- At this boundary the principal-recognition theorem is gone.  The remaining
-- chart-side datum is the scalar inclusion of the conservative 1/24 threshold
-- in the already-owned selected cut.  The other surviving frontier is the
-- concrete source/operator and CMP98 coordinate normalization.
literalCMP98SelectedCutStrongestFrontierRound176Level : ProofLevel
literalCMP98SelectedCutStrongestFrontierRound176Level = conditional
