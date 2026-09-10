{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBCurrentExact where

------------------------------------------------------------------------
-- FOCUSED CURRENT B ROLLUP
--
-- This is not a second planner.  It is the minimal current import surface after
-- the NS-R592 residual-normalization correction.  R304-R306 are now the shortest
-- standard-theorem mass-gap route.  R299-R303 retain the more explicit internal
-- subgap spectral reconstruction as an optional verification/producer route.
------------------------------------------------------------------------

import DASHI.Interop.IntrospectiveResidualNormalizationExact
import DASHI.Physics.YangMills.BalabanClayCanonicalMassGapConsumerRound270Exact
import DASHI.Physics.YangMills.BalabanClayDirectQuantitativeClusteringRound274Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound275Exact
import DASHI.Physics.YangMills.BalabanClayOneSidedCorrelationLimitRound276Exact
import DASHI.Physics.YangMills.BalabanFiniteRGToSpectrumCorrelationRound277Exact
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact
import DASHI.Physics.YangMills.BalabanExpectationCovarianceSpectrumWeldRound279Exact
import DASHI.Physics.YangMills.BalabanFiniteRGExpectationCovarianceSameObjectRound280Exact
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound282Exact
import DASHI.Physics.YangMills.BalabanFiniteVolumeReopeningPresentationRound283Exact
import DASHI.Physics.YangMills.BalabanCMP116DirectT5ContinuumClusteringRound284Exact
import DASHI.Physics.YangMills.BalabanClusteringDecayRatioToGapRound285Exact
import DASHI.Physics.YangMills.BalabanDirectCanonicalBCompletionRound286Exact
import DASHI.Physics.YangMills.BalabanCyclicContinuumCovarianceSpectrumRound287Exact
import DASHI.Physics.YangMills.BalabanSubgapSeparatingTimeRound288Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound289Exact
import DASHI.Physics.YangMills.BalabanCMP116TwoPhysicalJInsertionNormalizationRound290Exact
import DASHI.Physics.YangMills.BalabanDirectT5JInsertionShellAdapterRound291Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound292Exact

-- R293-R298: state-family source normalization, absolute-value correction,
-- direct T5 same-object construction, geometric subgap separation, actual
-- nonzero-mode construction, and the honest explicit-spectral min-cut.
import DASHI.Physics.YangMills.BalabanCMP116StateFamilyTwoJNormalizationRound293Exact
import DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound293Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound294Exact
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact
import DASHI.Physics.YangMills.BalabanCMP116TwoJMagnitudeCorrectionRound295Exact
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound298Exact

-- R299-R303: optional explicit spectral reconstruction.  Quantitative cyclicity
-- makes overlap amplitude positive by construction; positive component +
-- nonnegative remainder compiles the lower bound; one transfer E<->q coordinate
-- compiles both subgap/candidate rate semantics; R303 excludes positive subgap
-- modes directly.  These are no longer mandatory if the standard spectral
-- transfer theorem is imported.
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact
import DASHI.Physics.YangMills.BalabanQuantitativeSubgapSpectralCoreRound301Exact
import DASHI.Physics.YangMills.BalabanTransferEnergyDecayRatioCoordinateRound302Exact
import DASHI.Physics.YangMills.BalabanDirectPositiveSubgapExclusionRound303Exact

-- R304-R306: preferred shortest route.  R304 upgrades the arbitrary finite T5
-- shell to genuine two-observable continuum Euclidean-time clustering.  R305
-- removes a stale unused vacuum field from the standard transfer ABI and keeps
-- physical mass/rate meaning separate from the q=1/2 ratio.  R306 records the
-- three YM-specific payments G1-G3; clustering->spectrum is standard library
-- debt rather than new four-dimensional YM analysis.
import DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact
import DASHI.Physics.YangMills.BalabanPairwiseClusteringStandardMassGapRound305Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound306Exact

-- Older producer tactics retained below the canonical consumer.
import DASHI.Physics.YangMills.BalabanLangevinDirectInfluencePaymentRound271Exact
import DASHI.Physics.YangMills.BalabanPreferredRowCSpatialFrontierRound272Exact
import DASHI.Physics.YangMills.BalabanLangevinMarkedRowInfluenceAdapterRound273Exact
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormAttributionExact
import DASHI.Physics.YangMills.BalabanMassGapSurvival
