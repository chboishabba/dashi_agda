{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveLinkStrongestProducerRound169Exact where

------------------------------------------------------------------------
-- ROUND169 A1 BIDI: STRONGEST PRODUCER FROM POSITIVE LINK SMALLNESS ONLY
--
-- R168 proves negative/oriented traversal smallness from positive-bond
-- smallness plus inverse-invariance of the defect.  Therefore the strongest
-- analytic Eq. (119) producer should not expose R164's signed-link field.
--
-- This adapter composes R168 -> R164 -> R165 -> R166 -> R167.  Its quantitative
-- physical input is exactly the natural lattice-gauge source surface: the
-- stored positive bonds are small.  All negative traversal bounds are generated.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact as R159
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPrincipalChartRound166Exact as R166
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralDefectProducerRound167Exact as R167
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveLinkDefectRound168Exact as R168

positiveLinkOneStepDerivative :
  ∀ {C n Value group Radius}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (positive : R168.PositiveLinkDefectInputs source)
    (recognition : R166.DefectRecognizedPrincipalChart
      source (R168.asLiteralRelativeDefectInputs source positive)) →
  R159.UniformAdjointDifferentialCalculus
    (R126.Vector (R146.additive C)) →
  R126.OneStepAveragingDerivative (R146.additive C)
positiveLinkOneStepDerivative source positive recognition calculus =
  R167.literalDefectOneStepDerivative
    source
    (R168.asLiteralRelativeDefectInputs source positive)
    recognition
    calculus

positiveLinkMultiscaleDerivative :
  ∀ {C n Value group Radius}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (positive : R168.PositiveLinkDefectInputs source)
    (recognition : R166.DefectRecognizedPrincipalChart
      source (R168.asLiteralRelativeDefectInputs source positive)) →
  R159.UniformAdjointDifferentialCalculus
    (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
positiveLinkMultiscaleDerivative source positive recognition calculus =
  R167.literalDefectMultiscaleDerivative
    source
    (R168.asLiteralRelativeDefectInputs source positive)
    recognition
    calculus

cmp98Equation119PositiveLinkStrongestProducerRound169Level : ProofLevel
cmp98Equation119PositiveLinkStrongestProducerRound169Level = machineChecked

-- Remaining same-object leaf on the defect side:
--   the positive bond field of `source.realization` is the selected physical
--   Balaban background already carrying the repository's relaxed-radius theorem.
-- The signed path, inverse links, 74-link relative product and chart threshold
-- are no longer independent obligations.
literalCMP98SelectedBackgroundPositiveBondWeldRound169Level : ProofLevel
literalCMP98SelectedBackgroundPositiveBondWeldRound169Level = conditional
