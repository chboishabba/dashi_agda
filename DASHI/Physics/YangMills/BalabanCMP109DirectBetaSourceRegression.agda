module DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceRegression where

------------------------------------------------------------------------
-- Focused elaboration root for the current Row-A1 source-facing route.
--
-- Primary source:
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223
--
-- Background/averaging sources:
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", CMP 99 (1985), 389--434. DOI: 10.1007/BF01240355.
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- CMP 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- CURRENT HIGHEST-ALPHA SOURCE ROUTE
--
-- CMP109 Sect. 2 linearizes the nonlinear fluctuation averaging before the
-- Gaussian stage.  The delta constraint is then the fixed linear delta(Q B'),
-- constrained coordinates are eliminated as B' = C(U) B, and the covariance is
--
--     (C(U)^* A(U) C(U))^-1.
--
-- Hence the authoritative first variation is
--
--     D(C* A C) = C'* A C + C* A' C + C* A C',
--
-- not an abstract derivative of a moving delta-constraint.  A' contains the
-- literal background derivative of the CMP99 quadratic operator (the Wilson
-- Hessian contribution is a mixed third Wilson variation); C' is determined by
-- differentiating the eliminated-coordinate equation Q(U) C(U) = 0.
--
-- On the remainder side, beta_j is projected from the current E^(j+1), which
-- already depends on preceding couplings.  If the five-channel quartic bound is
-- uniform over the admissible history, history is an argument of betaInt rather
-- than a second additive final debt.  The final margin then collapses to
--
--     b_patch - C_beta gamma^4 > 0.
--
-- Existing quartic absorption algebra proves positivity once
-- C_beta gamma^4 <= b_patch/2.  Thus explicit decimal C_beta is not intrinsically
-- required: a finite history-uniform C_beta and a positive source-uniform patch
-- floor are sufficient once a small-coupling threshold is produced.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel; conditional)
open import DASHI.Physics.YangMills.BalabanCMP109SourceTranscriptionExact
open import DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceCutsetExact
open import DASHI.Physics.YangMills.BalabanCMP109A1CrossPollinatedDebtProducersExact
open import DASHI.Physics.YangMills.BalabanCMP109GaussianPositivePatchCorrectionExact
open import DASHI.Physics.YangMills.BalabanCMP109CorrectedPatchMarginCrossProverExact
open import DASHI.Physics.YangMills.BalabanCMP109FixedConstraintCoordinateGaussianExact
open import DASHI.Physics.YangMills.BalabanA1HistoryUniformRemainderAntiDoubleCountExact
open import DASHI.Physics.YangMills.BalabanCMP109QRConstraintAnnihilatorReductionExact
open import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound82FiveAnalyticLeafExact

------------------------------------------------------------------------
-- Current authoritative Gaussian source blockers
------------------------------------------------------------------------

literalCoordinateEmbeddingVariationRegressionLevel : ProofLevel
literalCoordinateEmbeddingVariationRegressionLevel =
  cmp109LiteralCoordinateEmbeddingVariationLevel

literalQuadraticOperatorVariationRegressionLevel : ProofLevel
literalQuadraticOperatorVariationRegressionLevel =
  cmp109LiteralQuadraticOperatorVariationLevel

literalRestrictedThreeTermVariationRegressionLevel : ProofLevel
literalRestrictedThreeTermVariationRegressionLevel =
  cmp109LiteralRestrictedThreeTermVariationLevel

literalCoordinateJacobianContributionRegressionLevel : ProofLevel
literalCoordinateJacobianContributionRegressionLevel =
  cmp109LiteralCoordinateJacobianContributionLevel

-- Within A', D_background Delta_Wilson is a mixed THIRD variation of the Wilson
-- action.  Existing literal first/second plaquette jets are ancestry, not this
-- final producer.
literalWilsonMixedThirdVariationRegressionLevel : ProofLevel
literalWilsonMixedThirdVariationRegressionLevel = conditional

literalMixedVertexPositivePatchRegressionLevel : ProofLevel
literalMixedVertexPositivePatchRegressionLevel =
  cmp109LiteralPositivePatchCurrentLevel

------------------------------------------------------------------------
-- Current remainder/history blocker
------------------------------------------------------------------------

literalFiveChannelTaylorInstantiationRegressionLevel : ProofLevel
literalFiveChannelTaylorInstantiationRegressionLevel =
  cmp109LiteralFiveChannelTaylorInstantiationLevel

literalFiveChannelQuotientMajorantRegressionLevel : ProofLevel
literalFiveChannelQuotientMajorantRegressionLevel =
  cmp109LiteralFiveChannelCurrentLevel

literalFiveChannelUniformOverHistoryRegressionLevel : ProofLevel
literalFiveChannelUniformOverHistoryRegressionLevel =
  cmp109LiteralFiveChannelUniformOverHistoryLevel

------------------------------------------------------------------------
-- Machine-checked reusable compilers
------------------------------------------------------------------------

historyUniformAntiDoubleCountRegressionLevel : ProofLevel
historyUniformAntiDoubleCountRegressionLevel =
  historyUniformCurrentRemainderAntiDoubleCountLevel

positivePatchArithmeticRegressionLevel : ProofLevel
positivePatchArithmeticRegressionLevel = positivePatchArithmeticLevel

fiveChannelQuarticDebtReuseRegressionLevel : ProofLevel
fiveChannelQuarticDebtReuseRegressionLevel =
  cmp109FiveChannelQuarticDebtReuseLevel

qrConstraintAnnihilatorReductionRegressionLevel : ProofLevel
qrConstraintAnnihilatorReductionRegressionLevel =
  cmp109QRConstraintAnnihilatorReductionLevel

------------------------------------------------------------------------
-- Conditional simplification / fallback paths
------------------------------------------------------------------------

-- KKT annihilation may simplify the C' connection terms, but only after the KKT
-- projector is identified with the SAME fixed-coordinate constrained Gaussian.
kktProjectionToConstrainedTraceWeldRegressionLevel : ProofLevel
kktProjectionToConstrainedTraceWeldRegressionLevel =
  cmp109KKTProjectionToConstrainedTraceWeldLevel

-- If history-uniform current-remainder control fails, the older explicit
-- localized/marginal history budget remains available as a failure-closed path.
literalLocalizedHistoryFallbackLevel : ProofLevel
literalLocalizedHistoryFallbackLevel = cmp109LiteralLocalizedMemoryCurrentLevel

literalMarginalHistoryFallbackLevel : ProofLevel
literalMarginalHistoryFallbackLevel = cmp109LiteralMarginalMemoryBoundCurrentLevel

------------------------------------------------------------------------
-- Cross-prover-only Lean theorem surfaces
------------------------------------------------------------------------

wilsonCubicCornerDisqualificationCrossProverRegressionLevel : ProofLevel
wilsonCubicCornerDisqualificationCrossProverRegressionLevel =
  cmp109WilsonCubicCornerDisqualificationCrossProverLevel

singleModeUniformFloorNoGoCrossProverRegressionLevel : ProofLevel
singleModeUniformFloorNoGoCrossProverRegressionLevel =
  cmp109SingleModeUniformFloorNoGoCrossProverLevel

quarterPatchLowerBoundCrossProverRegressionLevel : ProofLevel
quarterPatchLowerBoundCrossProverRegressionLevel =
  cmp109QuarterPatchLowerBoundCrossProverLevel

universalCoefficientCircularityCrossProverRegressionLevel : ProofLevel
universalCoefficientCircularityCrossProverRegressionLevel =
  cmp109UniversalCoefficientCircularityAuditCrossProverLevel

------------------------------------------------------------------------
-- Scoreboards
------------------------------------------------------------------------

round82HistoricalLeafCountRegression : Nat
round82HistoricalLeafCountRegression = round82ActualNewAnalyticLeafCount

-- Current frozen research scoreboard remains A/B/C/D = 4.
currentFrozenResearchCountRegression : Nat
currentFrozenResearchCountRegression = currentFrozenResearchCount
