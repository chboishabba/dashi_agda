{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBCurrentExact where

------------------------------------------------------------------------
-- FOCUSED CURRENT B ROLLUP
--
-- R304-R306 are the preferred shortest standard-theorem mass-gap route.
-- R299-R305 also retain the explicit mode/spectral reconstruction as an
-- independent audit.  Both routes share the exact finite T5 source carrier.
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
import DASHI.Physics.YangMills.BalabanCMP116StateFamilyTwoJNormalizationRound293Exact
import DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound294Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound294Exact
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact
import DASHI.Physics.YangMills.BalabanCMP116TwoJMagnitudeCorrectionRound295Exact
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound298Exact
import DASHI.Physics.YangMills.BalabanAbsoluteTwoJSourceMinCutRound299Exact
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact
import DASHI.Physics.YangMills.BalabanQuantitativeSubgapSpectralCoreRound301Exact
import DASHI.Physics.YangMills.BalabanLocalEnergyDecayRatioRound301Exact
import DASHI.Physics.YangMills.BalabanTransferEnergyDecayRatioCoordinateRound302Exact
import DASHI.Physics.YangMills.BalabanModeIndexedSpectralContradictionRound302Exact
import DASHI.Physics.YangMills.BalabanDirectPositiveSubgapExclusionRound303Exact
import DASHI.Physics.YangMills.BalabanModeSelectedDirectT5ContinuumUpperRound304Exact
import DASHI.Physics.YangMills.BalabanDirectT5PositiveSubgapExclusionRound305Exact
import DASHI.Physics.YangMills.BalabanModeIndexedPositiveGapCoreRound306Exact
import DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact
import DASHI.Physics.YangMills.BalabanPairwiseClusteringStandardMassGapRound305Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound306Exact
import DASHI.Physics.YangMills.BalabanCMP116SelectedJApplicabilityRound309Exact
import DASHI.Physics.YangMills.BalabanPairwiseEuclideanSemanticsRound310Exact
import DASHI.Physics.YangMills.BalabanPairwiseMassRateFromTransferCoordinateRound311Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound312Exact
import DASHI.Physics.YangMills.BalabanDirectR295ToR296MagnitudeCompilerRound313Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound314Exact
import DASHI.Physics.YangMills.BalabanPairwiseWilsonBoundedTestsRound315Exact
import DASHI.Physics.YangMills.BalabanHalfRateTransferCoordinateMassGapRound316Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound317Exact
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound319Exact
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound320Exact
import DASHI.Physics.YangMills.BalabanCMP109SelectedT5SameObjectRound321Exact
import DASHI.Physics.YangMills.BalabanCMP116SelectedJDomainApplicationRound322Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound323Exact
import DASHI.Physics.YangMills.BalabanCMP116SelectedJSourceMinCutRound324Exact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound325Exact
import DASHI.Physics.YangMills.BalabanCMP116SelectedJApplicabilityMinCutRound326Exact
import DASHI.Physics.YangMills.BalabanCMP116SelectedJCommonDomainRound327Exact
import DASHI.Physics.YangMills.BalabanCMP116PublishedAuthoritySelectedT5ApplicationExact
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound328Exact

-- R329 is the debt-kind normalization after the source-native H1 correction.
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound329Exact

-- R330 cross-pollinates the generic NS sequential-order closure into H2c and
-- records the source/application status of the five surviving coordinates.
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound330Exact

-- R331 repairs the historical "same Hamiltonian" carrier: the preferred
-- transfer coordinate is indexed by the actual OS reconstruction and retains a
-- proof-bearing TransferCoordinateOf relation before projecting to R311.
import DASHI.Physics.YangMills.BalabanOSIndexedTransferCoordinateRound331Exact

-- R332 removes the arbitrary time-translation function: pairwise translated
-- tests are definitionally produced by the SAME Euclidean-covariance/OS1
-- translation action; only physical time/support meaning remains to be paid.
import DASHI.Physics.YangMills.BalabanOSIndexedPairwiseEuclideanSemanticsRound332Exact

-- R333 composes the repaired H2a/H2b/H2c/H3 interfaces all the way through
-- R304/R316.  It creates no new theorem debt; H1 remains upstream in the exact
-- finite T5 presentation, while the four downstream application coordinates are
-- now one executable compiler route.
import DASHI.Physics.YangMills.BalabanCanonicalBOSIndexedCompletionRound333Exact

-- R334 corrects an over-coarse H1 application shortcut.  A scale/volume-level
-- common source-domain witness cannot by itself manufacture admissibility of
-- the actual selected pair (J_A,J_B); the pair-specific same-object domain weld
-- is proof-relevant and remains the source/application frontier.
import DASHI.Physics.YangMills.BalabanCMP116SelectedJPairDomainWeldRound334Exact

-- R335 factors that selected-pair weld through a source-native common-J pair
-- domain authority.  This demotes the selected-T5 pair weld from an independent
-- physical theorem: the surviving acquisition tasks are source-domain
-- transcription/alignment plus literal physical observable -> CMP116 J meaning.
import DASHI.Physics.YangMills.BalabanCMP116SelectedJPairDomainSourceFactorRound335Exact

-- R336 corrects one dependency overcount: once the unlocalized selected-T5 base
-- exists, its proof-bearing LiteralTwoSourceInsertionMeaning is already carried
-- as the `meaning` coordinate.  Constructing that base still requires the
-- physical same-density source semantics; it is simply not charged again after
-- the base has been built.
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound336Exact

-- Optional producer families and provenance snowballs retained below the
-- canonical consumer.  The source snowball is attribution/search metadata plus
-- historical donor classification only; it does not promote Step-V to a
-- mandatory route or import theorem content from citations.
import DASHI.Physics.YangMills.BalabanStepVConnectedCorrelationSourceSnowballExact
import DASHI.Physics.YangMills.BalabanStepVMarkedSourceDirectClusteringProducerCurrentExact
import DASHI.Physics.YangMills.BalabanUrsellToSubgapClusteringUpperBidiExact
import DASHI.Physics.YangMills.BalabanClayCanonicalBUrsellDonorBidiExact
import DASHI.Physics.YangMills.BalabanLangevinDirectInfluencePaymentRound271Exact
import DASHI.Physics.YangMills.BalabanPreferredRowCSpatialFrontierRound272Exact
import DASHI.Physics.YangMills.BalabanLangevinMarkedRowInfluenceAdapterRound273Exact
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormAttributionExact
import DASHI.Physics.YangMills.BalabanMassGapSurvival
