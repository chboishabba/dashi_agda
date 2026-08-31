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
-- Gaussian stage.  Constrained coordinates are eliminated as B'=C(U)B and the
-- covariance is
--
--     (C(U)^* A(U) C(U))^-1.
--
-- Hence
--
--     D(C*AC) = C'*AC + C*A'C + C*AC'.
--
-- This root now uses the source-native split rather than the older W/Q/R patch:
--
--   middle physical term  = C*A'C,
--   tangential C'          = C K, cancelled with induced volume Jacobian,
--   normal C'              = genuine constrained-subspace motion.
--
-- The Wilson part of A' has a literal physical mixed s t^2 quaternion jet.  A
-- four-link plaquette contains exactly 4^3=64 noncommutative Leibniz atoms and
-- the Wilson scalar coefficient is proved equal to their finite sum.  CMP99's
-- left-background tangent convention is bridged exactly to the repository's
-- right-exponential physical Hessian convention.
--
-- C' obeys Q C'=-Q'C.  Since CMP99's C is identity off selected eliminated
-- pivot bonds, each pivot derivative is exactly
--
--     C'_c = - a_c^-1 (Q' C)_c.
--
-- Pure tangential coordinate motion is no longer an analytic debt: exact finite
-- rational trace algebra proves
--
--   tr(Ahat^-1(K^T Ahat + Ahat K)) = 2 tr K.
--
-- Once the source change-of-variables density is identified with the induced
-- coordinate volume, this cancels its +tr K Jacobian response.  The active
-- positive-patch floor is therefore
--
--     b_fixed = b_middle - B_normal,
--
-- not b_W - |Q|-|R|.
--
-- On the finite-g side, if the five-channel betaInt bound is uniform over the
-- admissible preceding-coupling history, history is an argument of the CURRENT
-- remainder rather than a second additive final debt.  Then
--
--     beta >= b_fixed - C_beta gamma^4.
--
-- Explicit small-coupling arithmetic is closed constructively:
--
--     gamma* = (1/2) b_fixed / (C_beta + b_fixed)
--
-- absorbs C_beta gamma*^4 into b_fixed/2 whenever b_fixed>0 and C_beta>=0.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)
open import DASHI.Physics.YangMills.BalabanCMP109SourceTranscriptionExact
open import DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceCutsetExact
open import DASHI.Physics.YangMills.BalabanCMP109A1CrossPollinatedDebtProducersExact
open import DASHI.Physics.YangMills.BalabanCMP109CorrectedPatchMarginCrossProverExact
open import DASHI.Physics.YangMills.BalabanCMP109FixedConstraintCoordinateGaussianExact
open import DASHI.Physics.YangMills.BalabanCMP109EliminatedCoordinateDerivativeExact
open import DASHI.Physics.YangMills.BalabanCMP99EliminatedPivotDerivativeExact
open import DASHI.Physics.YangMills.BalabanA1HistoryUniformRemainderAntiDoubleCountExact
open import DASHI.Physics.YangMills.BalabanA1ExplicitSmallCouplingQuarticAbsorptionExact
open import DASHI.Physics.YangMills.BalabanCMP109QRConstraintAnnihilatorReductionExact
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonBackgroundQuadraticJetExact
open import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonBackgroundQuadraticJetExact
open import DASHI.Physics.YangMills.BalabanP33WilsonBackgroundTrivializationBridgeExact
open import DASHI.Physics.YangMills.BalabanFiniteRationalTraceConnectionCancellationExact
open import DASHI.Physics.YangMills.BalabanCMP109FixedCoordinateGaussianPositivePatchExact
open import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound82FiveAnalyticLeafExact

------------------------------------------------------------------------
-- Current authoritative Gaussian source blockers
------------------------------------------------------------------------

-- Literal one-step averaging derivative and its iteration are now the upstream
-- source leaves for normal constrained-subspace motion.
literalCMP98OneStepQPrimeRegressionLevel : ProofLevel
literalCMP98OneStepQPrimeRegressionLevel = cmp99LiteralQPrimeLevel

literalEliminatedPivotCoefficientRegressionLevel : ProofLevel
literalEliminatedPivotCoefficientRegressionLevel =
  cmp99LiteralEliminatedPivotCoefficientLevel

literalEliminatedPivotDerivativeRegressionLevel : ProofLevel
literalEliminatedPivotDerivativeRegressionLevel =
  cmp99LiteralEliminatedPivotDerivativeLevel

literalCoordinateEmbeddingVariationRegressionLevel : ProofLevel
literalCoordinateEmbeddingVariationRegressionLevel =
  cmp109LiteralCoordinateEmbeddingVariationLevel

literalQuadraticOperatorVariationRegressionLevel : ProofLevel
literalQuadraticOperatorVariationRegressionLevel =
  cmp109LiteralQuadraticOperatorVariationLevel

literalRestrictedThreeTermVariationRegressionLevel : ProofLevel
literalRestrictedThreeTermVariationRegressionLevel =
  cmp109LiteralRestrictedThreeTermVariationLevel

-- Tangential C' trace algebra is closed; only the source SAME-OBJECT measure
-- identification remains.
literalInducedCoordinateVolumeJacobianRegressionLevel : ProofLevel
literalInducedCoordinateVolumeJacobianRegressionLevel =
  cmp109LiteralInducedCoordinateVolumeJacobianLevel

literalNormalConnectionPatchBudgetRegressionLevel : ProofLevel
literalNormalConnectionPatchBudgetRegressionLevel =
  cmp99LiteralNormalConnectionPatchBudgetLevel

-- The generic and physical mixed-third Wilson bookkeeping and tangent
-- trivialization are no longer open.  The remaining Wilson source seams are
-- CMP99 operator normalization and the Fourier symbol of the same 64 atoms.
wilsonBackgroundQuadratic64AtomRegressionLevel : ProofLevel
wilsonBackgroundQuadratic64AtomRegressionLevel =
  physicalWilsonBackgroundQuadratic64AtomLevel

wilsonBackgroundTrivializationRegressionLevel : ProofLevel
wilsonBackgroundTrivializationRegressionLevel =
  wilsonBackgroundMixedJetTrivializationLevel

literalWilsonHessianBackgroundDerivativeIdentificationRegressionLevel : ProofLevel
literalWilsonHessianBackgroundDerivativeIdentificationRegressionLevel =
  cmp99WilsonHessianBackgroundDerivativeIdentificationLevel

literalMixedWilson64AtomFourierSymbolRegressionLevel : ProofLevel
literalMixedWilson64AtomFourierSymbolRegressionLevel =
  cmp99LiteralMixedWilson64AtomFourierSymbolLevel

literalFixedCoordinatePositivePatchRegressionLevel : ProofLevel
literalFixedCoordinatePositivePatchRegressionLevel =
  cmp109FixedCoordinateGaussianPositivePatchLevel

------------------------------------------------------------------------
-- Current remainder/history blockers
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

fiveChannelQuarticDebtReuseRegressionLevel : ProofLevel
fiveChannelQuarticDebtReuseRegressionLevel =
  cmp109FiveChannelQuarticDebtReuseLevel

eliminatedCoordinateDerivativeAlgebraRegressionLevel : ProofLevel
eliminatedCoordinateDerivativeAlgebraRegressionLevel =
  eliminatedCoordinateDerivativeAlgebraLevel

eliminatedPivotDerivativeAlgebraRegressionLevel : ProofLevel
eliminatedPivotDerivativeAlgebraRegressionLevel =
  cmp99EliminatedPivotDerivativeAlgebraLevel

tangentialConnectionTraceRegressionLevel : ProofLevel
tangentialConnectionTraceRegressionLevel =
  tangentialConnectionTraceCancellationLevel

fixedCoordinatePatchArithmeticRegressionLevel : ProofLevel
fixedCoordinatePatchArithmeticRegressionLevel = fixedCoordinatePatchArithmeticLevel

qrConstraintAnnihilatorReductionRegressionLevel : ProofLevel
qrConstraintAnnihilatorReductionRegressionLevel =
  cmp109QRConstraintAnnihilatorReductionLevel

------------------------------------------------------------------------
-- Conditional simplification / fallback paths
------------------------------------------------------------------------

-- KKT annihilation may simplify the remaining NORMAL C' contribution, but only
-- after its projector is identified with the same fixed-coordinate Gaussian.
kktProjectionToConstrainedTraceWeldRegressionLevel : ProofLevel
kktProjectionToConstrainedTraceWeldRegressionLevel =
  cmp109KKTProjectionToConstrainedTraceWeldLevel

-- Old W/Q/R patch is retained only as ancestry/cross-prover regression.  It is
-- no longer the authoritative source consumer after the C*AC recut.
historicalWQRPositivePatchRegressionLevel : ProofLevel
historicalWQRPositivePatchRegressionLevel = cmp109LiteralPositivePatchCurrentLevel

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
