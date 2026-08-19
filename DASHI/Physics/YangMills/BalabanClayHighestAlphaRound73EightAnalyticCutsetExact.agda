module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound73EightAnalyticCutsetExact where

------------------------------------------------------------------------
-- ROUND73: AUTHORITATIVE EIGHT-LEMMA ANALYTIC CUTSET
--
-- This root corrects one over-aggressive intermediate count.  Round72 had
-- already fused marked E^(2) localisation into `PhysicalUnifiedOneStepYMEstimate`.
-- Discovering that CMP109 itself owns the differentiated marked-decay shape
-- therefore SHRINKS lemma 4; it does not delete a ninth standalone item from
-- the already-eight-item cutset.
--
-- The literal five-role Clay compiler remains the endpoint authority.  The
-- shortest currently defensible ANALYTIC cutset beneath it is eight theorem-
-- sized jobs:
--
--  1 CompactSimpleSelectedBackgroundFiveBlockEstimate
--  2 LiteralWilsonFPHaarOneLoopRGCoefficient
--  3 LiteralStateEntersPublishedBalabanRG
--  4 PhysicalUnifiedOneStepYMEstimate
--  5 SameFamilyContinuumOSCompletion
--  6 SameDensityPolchinskiLangevinClustering
--  7 SameFamilyCompositeOPEStressWardClosure
--  8 FiniteScaleStrictFourthCumulantMargin
--
-- ROUND73 SHARPENINGS
--
-- * Lemma 4 does NOT re-prove ordinary finite-cutoff nonlinear RG stability.
--   CMP119 Sect.2 already puts the SAME complete density in an inductive class
--   containing the localized small-field E sector, strongly decaying R sector
--
--       |R^(j)(X)| <= g_j^kappa0 exp(-kappa0 d_j(X))            (2.31),
--
--   analytic localized boundary terms with
--
--       |B^(j)(X)| <= B exp(-kappa d_j(X))                      (2.42),
--
--   regular common analytic background domains and covariance control.
--   CMP119 Theorem 1 / CMP122 preserve that complete class when the running
--   couplings satisfy the source smallness hypothesis.  Once lemma 3 identifies
--   the literal state with this flow, these baseline small/large/locality
--   coordinates are SOURCE-OWNED.
--
-- * CMP109 already works at the twice-differentiated E^(2) level and, after
--   (4.35), carries the domain/free-boundary replacement through an additional
--   marked exponential factor; (4.36)--(4.37) resum it and (5.10) gives
--   positive exponential position-space decay of Pi.  Therefore lemma 4 only
--   needs SAME-OBJECT identification of source E^(2)/Pi with the unified
--   derivative/Hessian coordinate, plus genuinely extra Clay consumers:
--   composite insertions and separation-weighted connected correlations with a
--   common quantitative increment modulus.
--
-- * The exact 17/32 tail already gives the common Cauchy modulus.  Once ONE
--   completed unified state exists, `BalabanUnifiedCompletedStateProjectionExact`
--   proves that ordinary/composite/correlation limits are projections of that
--   SAME state.  Thus lemma 5 cannot splice unrelated subsequences; its live
--   content is one physical completed state + limiting measure/Schwinger
--   identification + continuum Euclidean/OS closure.
--
-- * Lemma 6 has no independent compact-Lie connection-growth estimate.  A
--   compact Lie group admits an Ad-invariant inner product; ad_Z is skew, and
--   the onsite connection contribution to quadratic derivative energy vanishes
--   exactly.  The only nonlocal growth budget is the SAME symmetric Hessian.
--
-- Thus Round73 removes duplicated mathematics INSIDE lemmas 4--6 without
-- pretending that continuum completion, physical clustering, OPE/stress, or
-- interacting survival have already been proved.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

-- Literal endpoint compiler.
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact

-- Published ordinary RG core / same-object seam.
import DASHI.Physics.YangMills.BalabanPublishedUVStabilityNonlinearRGCoreExact
import DASHI.Physics.YangMills.BalabanCMP122PublishedFourDimensionalUVStabilityExact
import DASHI.Physics.YangMills.Balaban1989CompleteDensityToYM4RegionExact
import DASHI.Physics.YangMills.Balaban1989CanonicalYM4StateFromSection2Exact

-- Differentiated source localisation and owned finite/quasi-local compilers.
import DASHI.Physics.YangMills.BalabanMarkedHessianPublishedDecayBoundaryExact
import DASHI.Physics.YangMills.BalabanDifferentiatedMarkedFactorProductExact
import DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact
import DASHI.Physics.YangMills.BalabanSourceExponentialToWeightedHessianExact

-- Unified norm / exact 17/32 tail / one completed state projection.
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact
import DASHI.Physics.YangMills.BalabanUnifiedPolymerStepVContractionBudgetExact
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondTailModulusExact
import DASHI.Physics.YangMills.BalabanUnifiedCompletedStateProjectionExact

-- Mass-gap route and basis-free compact-Lie cancellation.
import DASHI.Physics.YangMills.BalabanPolchinskiMultiscaleLSIBridgeExact
import DASHI.Physics.YangMills.BalabanUnifiedPolchinskiCurvatureDebtExact
import DASHI.Physics.YangMills.CompactLieBiInvariantSkewLangevinExact
import DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact
import DASHI.Physics.YangMills.BalabanPoincareFiniteSpeedClusteringRateExact
import DASHI.Physics.YangMills.BalabanClayT5PhysicalContinuumOSGapBridgeExact

------------------------------------------------------------------------
-- SOURCE-OWNED / MACHINE-CONSTRUCTED SUBSTRUCTURE
------------------------------------------------------------------------

round73PublishedCompleteFiniteCutoffRGLevel : ProofLevel
round73PublishedCompleteFiniteCutoffRGLevel = standardImported

round73PublishedDifferentiatedMarkedE2DecayLevel : ProofLevel
round73PublishedDifferentiatedMarkedE2DecayLevel = standardImported

round73FiniteMarkedOperatorAssemblyLevel : ProofLevel
round73FiniteMarkedOperatorAssemblyLevel = machineChecked

round73ExponentialToWeightedHessianLevel : ProofLevel
round73ExponentialToWeightedHessianLevel = machineChecked

round73SeventeenThirtySecondTailLevel : ProofLevel
round73SeventeenThirtySecondTailLevel = machineChecked

round73OneCompletedStateProjectsToAllConsumersLevel : ProofLevel
round73OneCompletedStateProjectsToAllConsumersLevel = machineChecked

round73CompactLieSkewConnectionEnergyZeroLevel : ProofLevel
round73CompactLieSkewConnectionEnergyZeroLevel = machineChecked

------------------------------------------------------------------------
-- THE EIGHT LIVE ANALYTIC JOBS
------------------------------------------------------------------------

compactSimpleSelectedBackgroundFiveBlockEstimateLevel : ProofLevel
compactSimpleSelectedBackgroundFiveBlockEstimateLevel = conditional

literalWilsonFPHaarOneLoopRGCoefficientLevel : ProofLevel
literalWilsonFPHaarOneLoopRGCoefficientLevel = conditional

literalStateEntersPublishedBalabanRGLevel : ProofLevel
literalStateEntersPublishedBalabanRGLevel = conditional

-- STRONG EXTENSION only: source Section-2 flow + source E^(2) coordinate ->
-- one unified state additionally controlling composite insertions and
-- separation-weighted connected correlations with the common scale modulus.
physicalUnifiedOneStepYMEstimateLevel : ProofLevel
physicalUnifiedOneStepYMEstimateLevel = conditional

-- One completed unified state; identify its ordinary projection with the
-- Schwinger family of one limiting measure and establish thermodynamic/
-- continuum Euclidean/OS closure.  Projected observable limits are downstream.
sameFamilyContinuumOSCompletionLevel : ProofLevel
sameFamilyContinuumOSCompletionLevel = conditional

sameDensityPolchinskiLangevinClusteringLevel : ProofLevel
sameDensityPolchinskiLangevinClusteringLevel = conditional

sameFamilyCompositeOPEStressWardClosureLevel : ProofLevel
sameFamilyCompositeOPEStressWardClosureLevel = conditional

finiteScaleStrictFourthCumulantMarginLevel : ProofLevel
finiteScaleStrictFourthCumulantMarginLevel = conditional

------------------------------------------------------------------------
-- COUNT BOUNDARY
-- Five = Clay-facing endpoint roles.
-- Eight = current theorem-sized analytic jobs below those roles.
-- Any future count reduction must prove an implication between these jobs, not
-- merely rename their conjunction.
------------------------------------------------------------------------
