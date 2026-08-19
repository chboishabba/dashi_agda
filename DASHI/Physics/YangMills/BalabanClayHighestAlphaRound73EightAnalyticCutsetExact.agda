module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound73EightAnalyticCutsetExact where

------------------------------------------------------------------------
-- ROUND73: AUTHORITATIVE EIGHT-LEMMA ANALYTIC CUTSET
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
--  6 SameDensityCompactLieHeatLangevinClustering
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
--   forces ordinary/composite/correlation limits to be projections of that SAME
--   state.  Lemma 5's live content is one physical completed state + limiting
--   measure/Schwinger identification + continuum Euclidean/OS closure.
--
-- * Lemma 6 no longer silently applies the BBD Euclidean/Gaussian Polchinski
--   theorem to G^E.  BBD starts from X subset R^N.  The PRIMARY physical route
--   is now the compact-manifold Haar heat/Doob flow on the literal group carrier:
--
--       u_t = H_t exp(-V_0),       V_t = -log u_t,
--
--   with curvature coordinate
--
--       (1/2) Ric + Hess V_t.
--
--   A finite accumulated negative-curvature debt yields an LSI through the
--   inhomogeneous heat/Doob criterion.  The old BBD module is retained only as
--   an optional chart/globalisation route behind an explicit linear-carrier
--   theorem.
--
-- * The compact-Lie connection term still needs no positive growth budget.  An
--   Ad-invariant inner product makes ad_Z skew, so its quadratic derivative-
--   energy contribution vanishes sitewise.  Spatial propagation is controlled
--   by the SAME symmetric quasi-local Hessian coordinate.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact

import DASHI.Physics.YangMills.BalabanPublishedUVStabilityNonlinearRGCoreExact
import DASHI.Physics.YangMills.BalabanCMP122PublishedFourDimensionalUVStabilityExact
import DASHI.Physics.YangMills.Balaban1989CompleteDensityToYM4RegionExact
import DASHI.Physics.YangMills.Balaban1989CanonicalYM4StateFromSection2Exact

import DASHI.Physics.YangMills.BalabanMarkedHessianPublishedDecayBoundaryExact
import DASHI.Physics.YangMills.BalabanDifferentiatedMarkedFactorProductExact
import DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact
import DASHI.Physics.YangMills.BalabanSourceExponentialToWeightedHessianExact

import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact
import DASHI.Physics.YangMills.BalabanUnifiedPolymerStepVContractionBudgetExact
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondTailModulusExact
import DASHI.Physics.YangMills.BalabanUnifiedCompletedStateProjectionExact

-- Primary group-native mass-gap route.
import DASHI.Physics.YangMills.CompactLieHeatDoobMultiscaleLSIExact
import DASHI.Physics.YangMills.CompactLieBiInvariantSkewLangevinExact
import DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact
import DASHI.Physics.YangMills.BalabanPoincareFiniteSpeedClusteringRateExact
import DASHI.Physics.YangMills.BalabanClayT5PhysicalContinuumOSGapBridgeExact

-- Optional Euclidean/chart calibration only; not a direct physical import.
import DASHI.Physics.YangMills.BalabanPolchinskiMultiscaleLSIBridgeExact

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

-- STRONG EXTENSION only: published Section-2 flow + source E^(2) coordinate ->
-- one unified state additionally controlling composite insertions and
-- separation-weighted connected correlations with the common scale modulus.
physicalUnifiedOneStepYMEstimateLevel : ProofLevel
physicalUnifiedOneStepYMEstimateLevel = conditional

sameFamilyContinuumOSCompletionLevel : ProofLevel
sameFamilyContinuumOSCompletionLevel = conditional

-- On the literal G^E carrier: construct the heat-renormalised potential V_t,
-- prove volume-uniform integrable lower curvature history for
-- (1/2 Ric + Hess V_t), then use the SAME Hessian for compact-Lie derivative
-- propagation and obtain spatial covariance decay before OS reconstruction.
sameDensityCompactLieHeatLangevinClusteringLevel : ProofLevel
sameDensityCompactLieHeatLangevinClusteringLevel = conditional

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
