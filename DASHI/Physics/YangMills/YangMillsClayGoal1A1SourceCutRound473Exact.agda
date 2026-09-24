{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayGoal1A1SourceCutRound473Exact where

------------------------------------------------------------------------
-- GOAL-1 A1 / ROUND473: EXACT CURRENT-STEP BETA SOURCE CUT.
--
-- The old A1 presentation mixed together:
--   * source W/Q/R operator differentiation,
--   * extraction of the constrained Gaussian mixed coefficient,
--   * five finite-g channels,
--   * one-loop regular Brillouin remainder,
--   * and final positive-beta arithmetic.
--
-- Existing compilers remove everything after the literal source calculations.
-- The surviving physical calculations are:
--
--   A1a  build the literal CMP99/CMP98/CMP109 W/Q/R first-variation symbols and
--        prove the constrained pointwise W+Q+R assembly;
--
--   A1b  identify betaZ with the negative mixed coefficient of that SAME
--        constrained Gaussian Eq.(5.1) symbol;
--
--   A1c  identify the SAME physical two-jet finite-g part with the declared five
--        channels;
--
--   A1d  evaluate the literal Wilson/FP/Haar regular contribution by four joint
--        certified receipt totals and identify beta = C_A*11/24 + that SAME
--        receipt-bounded remainder.
--
-- R117/R123 compile A1a--A1c to Eq.(5.42)/the history beta certificate.
-- R471 compiles A1d to an all-compact-simple strictly positive beta enclosure.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP109GaussianFirstVariationSourceDecompositionExact as WQR
import DASHI.Physics.YangMills.BalabanA1WQRPhysicalJetRound123Exact as R123
import DASHI.Physics.YangMills.BalabanA1FiveChannelEvaluatorBidiRound117Exact as R117
import DASHI.Physics.YangMills.BalabanLiteralFourReceiptBetaRound471Exact as R471

a1aLiteralWilsonHessianVariationLevel : ProofLevel
a1aLiteralWilsonHessianVariationLevel =
  WQR.cmp109LiteralWilsonHessianVariationLevel

a1aLiteralAveragingConstraintVariationLevel : ProofLevel
a1aLiteralAveragingConstraintVariationLevel =
  WQR.cmp109LiteralAveragingConstraintVariationLevel

a1aLiteralGaugeProjectionVariationLevel : ProofLevel
a1aLiteralGaugeProjectionVariationLevel =
  WQR.cmp109LiteralGaugeProjectionVariationLevel

a1aLiteralWQRAssemblyLevel : ProofLevel
a1aLiteralWQRAssemblyLevel =
  WQR.cmp109LiteralWQRAssemblyLevel

a1bConstrainedGaussianMixedCoefficientLevel : ProofLevel
a1bConstrainedGaussianMixedCoefficientLevel =
  R123.literalA1ConstrainedGaussianMixedCoefficientLevel

a1cPhysicalJetFiveChannelSplitLevel : ProofLevel
a1cPhysicalJetFiveChannelSplitLevel =
  R117.literalA1PhysicalJetGaussianFiveChannelSplitLevel

a1dFourJointReceiptEvaluationLevel : ProofLevel
a1dFourJointReceiptEvaluationLevel =
  R471.literalRound471FourJointReceiptEvaluationLevel

a1WQRSplitCompilerLevel : ProofLevel
a1WQRSplitCompilerLevel =
  R123.a1WQRPointwiseToMixedCoefficientLevel

a1FiveChannelCertificateCompilerLevel : ProofLevel
a1FiveChannelCertificateCompilerLevel =
  R117.a1ReducedInputsToEquation542CompilerLevel

a1FourReceiptPositiveBetaCompilerLevel : ProofLevel
a1FourReceiptPositiveBetaCompilerLevel =
  R471.round471ReceiptToPositiveBetaCompilerLevel

round473A1SourceCutCompilerLevel : ProofLevel
round473A1SourceCutCompilerLevel = machineChecked

-- No additional beta-positivity or orbit-aggregation lemma remains after these
-- literal source calculations are supplied.
literalRound473A1SourceInstantiationLevel : ProofLevel
literalRound473A1SourceInstantiationLevel = conditional
