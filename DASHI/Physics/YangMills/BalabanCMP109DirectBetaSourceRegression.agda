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
--     D(C* A C) = C'* A C + C* A' C + C* A C'.
--
-- The Wilson part of A' is now represented by a literal physical mixed
-- background/fluctuation jet.  Its four-link plaquette product has exactly
-- 4^3=64 noncommutative Leibniz atoms, and the scalar Wilson coefficient is
-- proved equal to their exact finite sum.  A separate quaternion theorem bridges
-- CMP99's left-background tangent convention to the repository's right-
-- exponential physical Hessian convention.
--
-- C' is governed by the differentiated eliminated-coordinate identity
--
--     Q C' = - Q' C.
--
-- On the remainder side, beta_j is projected from the current E^(j+1), which
-- already depends on preceding couplings.  If the five-channel quartic bound is
-- uniform over admissible history, history is an argument of betaInt rather than
-- a second additive final debt.  The final margin is then
--
--     b_patch - C_beta gamma^4 > 0.
--
-- Explicit small-coupling arithmetic is no longer open: for b>0, C_beta>=0,
--
--     gamma* = (1/2) b / (C_beta + b)
--
-- satisfies C_beta gamma*^4 <= b/2.  Thus no fourth-root construction or
-- numerical search for gamma is needed after the two literal source constants
-- b_patch and C_beta have been produced uniformly on the same RG family.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)
open import DASHI.Physics.YangMills.BalabanCMP109SourceTranscriptionExact
open import DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceCutsetExact
open import DASHI.Physics.YangMills.BalabanCMP109A1CrossPollinatedDebtProducersExact
open import DASHI.Physics.YangMills.BalabanCMP109GaussianPositivePatchCorrectionExact
open import DASHI.Physics.YangMills.BalabanCMP109CorrectedPatchMarginCrossProverExact
open import DASHI.Physics.YangMills.BalabanCMP109FixedConstraintCoordinateGaussianExact
open import DASHI.Physics.YangMills.BalabanCMP109EliminatedCoordinateDerivativeExact
open import DASHI.Physics.YangMills.BalabanA1HistoryUniformRemainderAntiDoubleCountExact
open import DASHI.Physics.YangMills.BalabanA1ExplicitSmallCouplingQuarticAbsorptionExact
open import DASHI.Physics.YangMills.BalabanCMP109QRConstraintAnnihilatorReductionExact
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonBackgroundQuadraticJetExact
open import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonBackgroundQuadraticJetExact
open import DASHI.Physics.YangMills.BalabanP33WilsonBackgroundTrivializationBridgeExact
open import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound82FiveAnalyticLeafExact

------------------------------------------------------------------------
-- Current authoritative Gaussian source blockers
------------------------------------------------------------------------

literalCoordinateEmbeddingVariationRegressionLevel : ProofLevel
literalCoordinateEmbeddingVariationRegressionLevel =
  cmp109LiteralCoordinateEmbeddingVariationLevel

literalQPrimeRegressionLevel : ProofLevel
literalQPrimeRegressionLevel = cmp99LiteralQPrimeLevel

literalCPrimeFromConstraintRegressionLevel : ProofLevel
literalCPrimeFromConstraintRegressionLevel = cmp109LiteralCPrimeFromConstraintLevel

literalQuadraticOperatorVariationRegressionLevel : ProofLevel
literalQuadraticOperatorVariationRegressionLevel =
  cmp109LiteralQuadraticOperatorVariationLevel

literalRestrictedThreeTermVariationRegressionLevel : ProofLevel
literalRestrictedThreeTermVariationRegressionLevel =
  cmp109LiteralRestrictedThreeTermVariationLevel

literalCoordinateJacobianContributionRegressionLevel : ProofLevel
literalCoordinateJacobianContributionRegressionLevel =
  cmp109LiteralCoordinateJacobianContributionLevel

-- The generic and physical noncommutative mixed-third Wilson bookkeeping is no
-- longer open.  The remaining source seam is the exact CMP99 normalization /
-- operator identification inside A'(U).
wilsonBackgroundQuadratic64AtomRegressionLevel : ProofLevel
wilsonBackgroundQuadratic64AtomRegressionLevel =
  physicalWilsonBackgroundQuadratic64AtomLevel

wilsonBackgroundTrivializationRegressionLevel : ProofLevel
wilsonBackgroundTrivializationRegressionLevel =
  wilsonBackgroundMixedJetTrivializationLevel

literalWilsonHessianBackgroundDerivativeIdentificationRegressionLevel : ProofLevel
literalWilsonHessianBackgroundDerivativeIdentificationRegressionLevel =
  cmp99WilsonHessianBackgroundDerivativeIdentificationLevel

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

explicitSmallCouplingQuarticAbsorptionRegressionLevel : ProofLevel
explicitSmallCouplingQuarticAbsorptionRegressionLevel =
  explicitSmallCouplingQuarticAbsorptionLevel

positivePatchArithmeticRegressionLevel : ProofLevel
positivePatchArithmeticRegressionLevel = positivePatchArithmeticLevel

fiveChannelQuarticDebtReuseRegressionLevel : ProofLevel
fiveChannelQuarticDebtReuseRegressionLevel =
  cmp109FiveChannelQuarticDebtReuseLevel

eliminatedCoordinateDerivativeAlgebraRegressionLevel : ProofLevel
eliminatedCoordinateDerivativeAlgebraRegressionLevel =
  eliminatedCoordinateDerivativeAlgebraLevel

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
