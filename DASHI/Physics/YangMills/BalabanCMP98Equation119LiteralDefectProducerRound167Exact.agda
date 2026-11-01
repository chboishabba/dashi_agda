{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralDefectProducerRound167Exact where

------------------------------------------------------------------------
-- ROUND167 A1 BIDI: STRONGEST EQ. (119) PRODUCER NO LONGER USES THE GENERIC
-- PHYSICAL-PRINCIPAL-LOG WRAPPER
--
-- R164-R166 now provide the exact analytic route:
--
--   literal relative path
--     -> 74-link telescope
--     -> defect <= 37/1024 < 1/24
--     -> one standard principal-chart recognition theorem
--     -> principal Y_x with exp/log inverse.
--
-- R159 independently constructs the left/right g,g^-1 calculus from one
-- exp/log differential family plus adjoint transport.  This file composes those
-- two sides directly.  The consumer accepts no PhysicalSU2PrincipalLogMeaning,
-- no pointwise image receipt, no arbitrary Y_x/log, and no arbitrary LR family.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119ExistingPrincipalLogRound156Exact as R156
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact as R159
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralRelativeDefectRound164Exact as R164
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPrincipalChartRound166Exact as R166

literalDefectOneStepDerivative :
  ∀ {C n Value group Radius}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (defectInputs : R164.LiteralRelativeDefectInputs source)
    (recognition : R166.DefectRecognizedPrincipalChart source defectInputs) →
  R159.UniformAdjointDifferentialCalculus
    (R126.Vector (R146.additive C)) →
  R126.OneStepAveragingDerivative (R146.additive C)
literalDefectOneStepDerivative source defectInputs recognition calculus =
  R156.existingPrincipalLogOneStepDerivative
    (R158.asRound152Source source)
    (R166.chart recognition)
    (R159.asUniformLeftRightDexpFamily calculus)

literalDefectMultiscaleDerivative :
  ∀ {C n Value group Radius}
    (source : R158.CanonicalL13Equation119Source C n Value group)
    (defectInputs : R164.LiteralRelativeDefectInputs source)
    (recognition : R166.DefectRecognizedPrincipalChart source defectInputs) →
  R159.UniformAdjointDifferentialCalculus
    (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
literalDefectMultiscaleDerivative source defectInputs recognition calculus =
  R156.existingPrincipalLogMultiscaleDerivative
    (R158.asRound152Source source)
    (R166.chart recognition)
    (R159.asUniformLeftRightDexpFamily calculus)

cmp98Equation119LiteralDefectProducerRound167Level : ProofLevel
cmp98Equation119LiteralDefectProducerRound167Level = machineChecked

-- Strongest surviving physical/source inputs:
--   * actual periodic background realization with its selected per-link defect
--     theorem <= 1/2048;
--   * standard SU(2) recognition that operator defect <= 1/24 lies in the
--     principal chart;
--   * same-coordinate identification of the exp/log differential and adjoint
--     family with CMP98's printed iY normalization.
-- Everything from the relative path through Eq. (119) is now constructed.
literalCMP98PerLinkDefectInstantiationRound167Level : ProofLevel
literalCMP98PerLinkDefectInstantiationRound167Level = conditional

literalCMP98DifferentialNormalizationRound167Level : ProofLevel
literalCMP98DifferentialNormalizationRound167Level = conditional
