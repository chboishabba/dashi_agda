module DASHI.Unified.YMClayOriginalWilsonPhysicalRegression where

------------------------------------------------------------------------
-- Dedicated PHYSICAL original-Wilson finite-source regression root.
--
-- Typechecks the actual changing-cutoff SU(N) Wilson-Gibbs two-J jet,
-- its finite Haar numerator/normalization proofs, and the identical
-- n=3 R445 native blocked-pushforward -> R320 covariance chain.
--
-- Deliberately NOT marked --safe: original RealAnalysisAxioms (ℝ),
-- selected compact one-link Haar and exponential/division authorities
-- remain transitive physical assumptions, to be separately discharged
-- on concrete carriers.  No trust claim is inferred by this import.
--
-- Pair with the independent exact rational reference script and the
-- proof-relevant physical Y.01/Y.02 applicability obligations.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteTwoSourceJetExact as FiniteSource
import DASHI.Physics.YangMills.YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact as NativeBlockedSource
import DASHI.Physics.YangMills.YMClayOriginalWilsonAffineMarkedPartitionExact as OriginalAffineSource
import DASHI.Physics.YangMills.YMClayOriginalWilsonNativeMarkedPushforwardExact as NativeMarkedSource
import DASHI.Physics.YangMills.YMClaySUNOriginal64Pair896MarkedEffectiveSourceExact as EffectiveMarkedSource
import DASHI.Physics.YangMills.YMClayOriginalWilsonTwoPlaquetteMarkedSourceExact as PlaquetteMarkedSource
import DASHI.Physics.YangMills.YMClayOriginalWilsonNativeOSPullbackExact as NativeOSPullback
import DASHI.Physics.YangMills.YMClayCMP119122116SelectedProducerWeldExact as PublishedLocalizationCompiler

import DASHI.Physics.YangMills.YMClayOriginalR445ReflectedAllWordGramExact as NativeAllWordGram
import DASHI.Physics.YangMills.YMClayOriginalR445PublishedWilsonRPWordWeldExact as NativePublishedWilsonRP
import DASHI.Physics.YangMills.YMClayNativeClosedThreeEqualitiesCandidateExact as Original1024PermutationChecks

import DASHI.Physics.YangMills.YMClayNative1024ClosedReindexHaarConsequencesExact as Native1024Haar

import DASHI.Physics.YangMills.YMClayNative1024WeightedWilsonReindexExact as NativeWeightedWilson

import DASHI.Physics.YangMills.YMClayNative1024FullMarkedWilsonReindexExact as NativeFullMarkedWilson

import DASHI.Physics.YangMills.YMClayOriginalWilsonF19ConcreteWeightExact as PhysicalF19WilsonWeight

import DASHI.Physics.YangMills.YMClayNativePairsSpectatorsFubiniExact as OriginalFlatNestedFubini
import DASHI.Physics.YangMills.YMClayOriginalWilsonPhysicalF19PartitionExact as OriginalPhysicalF19Partition

import DASHI.Physics.YangMills.YMClayNativeR445TemporalReversalExact as NativeTimeReflection

import DASHI.Physics.YangMills.YMClayD1OriginalCovarianceToR320Exact as D1OriginalCovariance

import DASHI.Physics.YangMills.YMClayE1VariableCutoffCylinderLimitExact as E1VariableCutoffCylinder
import DASHI.Physics.YangMills.YMClayE1OriginalSUNDependentCylinderExact as E1OriginalSUNDependent

-- D1 exact ORIGINAL all-varying-cutoff real-valued Wilson covariance,
-- gauge-invariant test products, normalized expectation extensionality.
import DASHI.Physics.YangMills.YMClayOriginalVariableWilsonCovarianceSourceExact as D1VariableOriginalWilsonCovariance

import DASHI.Physics.YangMills.YMClayE1OriginalSUNFiniteCylinderLawsExact as E1NativeFiniteCylinderLaws

import DASHI.Physics.YangMills.YMClayD1OriginalRealCMP116VariableCutoffExact as D1OriginalRealCMP116

import DASHI.Physics.YangMills.YMClayD1OriginalFullWilsonSmallLargeFieldExact as D1FullWilsonSmallLarge

-- E1.02 / D1.02: all finite gauge-invariant plaquette words on actual
-- changing-cutoff Wilson Gibbs measure; same original real two-J jet.
import DASHI.Physics.YangMills.YMClayE1D1OriginalVariablePlaquetteWordsExact as VariablePlaquetteWords

-- D1 constructive source conflict: actual shared native plaquette witness.
import DASHI.Physics.YangMills.YMClayD1OriginalConflictPlaquetteWitnessExact as D1NativeConflictWitness

-- D1 distinct original marked-link 19-count transport, with native degree-18 leaf explicit.
import DASHI.Physics.YangMills.YMClayD1OriginalGreedy19CountingExact as D1NativeGreedyCounting

-- D1 structurally terminating fuel-greedy, original-link maximality and 19-count transport.
import DASHI.Physics.YangMills.YMClayD1OriginalFuelGreedyTerminationExact as D1FuelGreedy

-- D1/P06 concrete same-Wilson-positive-bond conflict graph (nonempty original plaquette witness).
import DASHI.Physics.YangMills.YMClayD1OriginalLinkStarFiniteNeighbourGraphExact as D1P06OriginalLinkGraph

-- Canonical original-positive-bond deduplication: maximal independent greedy selection, set-cardinality 19 bound conditional on real degree-18.
import DASHI.Physics.YangMills.YMClayD1OriginalMarkedLinkDedupExact as D1OriginalMarkedLinkDedup

-- E1/A3: original changing-cutoff all-word Wilson values depend only on finite ACTUAL signed-path positive-link support.
import DASHI.Physics.YangMills.YMClayE1A3OriginalAllWordPathSupportExtensionalExact as E1A3AllWordSupport

-- E1/A3 literal finite List SUN-link-value coordinate projection and source-real Wilson word factorization.
import DASHI.Physics.YangMills.YMClayE1A3OriginalFiniteCoordinateProjectionExact as E1A3ActualFiniteProjection

-- E1/A3: actual original positive-link tuple evaluator reconstructs signed path holonomy and every real SU(N) plaquette word.
import DASHI.Physics.YangMills.YMClayE1A3OriginalSignedPathValueEvaluatorExact as E1A3DirectWordEvaluator

-- E1/A3: actual original Gibbs/Haar normalized expectation of finite positive-link tuple evaluation is the original Wilson E1 cylinder expectation.
import DASHI.Physics.YangMills.YMClayE1A3OriginalFiniteValueExpectationWeldExact as E1A3RealExpectationWeld

-- E1/A3 cross-cutoff cut: actual n=3 Wilson Gibbs state pulled back through native 4->2 SU(N) block equals the original R445 effective pushforward; coarse n=1 Wilson state remains independent.
import DASHI.Physics.YangMills.YMClayE1A3OriginalR445CrossCutoffSourceExact as E1A3ActualR445CrossCutoff

-- E1/D1 original RG maximal cut: three original Wilson coarse moments suffice to identify the exact R445 fine mixed-J source with the separately selected bare coarse connected covariance.
import DASHI.Physics.YangMills.YMClayE1D1OriginalR445ThreeMomentRGCutExact as E1D1OriginalR445ThreeMomentCut

-- E1/D1: quantitative real-valued three-moment original Wilson R445 RG residual using CMP116 finite-factor product telescope (scalar subtraction-rearrangement explicitly not silently assumed).
import DASHI.Physics.YangMills.YMClayE1D1OriginalR445QuantitativeThreeMomentRGCutExact as E1D1OriginalQuantitativeRGCut

-- Original Wilson physical source numerator order: all-cutoff positivity, signed-test congruence and partition majorant for positive-complement test, from native product Haar.
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteNumeratorOrderExact as OriginalWilsonNumeratorOrder

-- Original Wilson physical RG bounded-test majorants: original n=3 pushforward and n=1 bare expectation both <=1 from native product Haar.
import DASHI.Physics.YangMills.YMClayE1D1OriginalR445BoundedMomentMajorantsExact as E1D1OriginalBoundedMomentMajorants

-- E1/A3 physical one-step RG error: exact original interacting Wilson cross numerator and all-weight unit cancellation, without bare-action closure.
import DASHI.Physics.YangMills.YMClayE1A3OriginalR445WeightedCrossNumeratorExact as E1A3OriginalWeightedRGError

-- E1/D1: same original fine-blocked vs bare Wilson weighted cross numerator invariant under arbitrary scalar constant-mode shifts; subtraction centering requires explicit selected scalar law.
import DASHI.Physics.YangMills.YMClayE1D1CrossNumeratorCenteringExact as OriginalWilsonCrossNumeratorCentering

-- E1/D1 P0.01--04 original Wilson bare-centering and exact positive-partition quotient; selected real additive/quotient laws remain explicit and not newly postulated.
import DASHI.Physics.YangMills.YMClayE1D1CrossNumeratorCenteringAlgebraExact as OriginalWilsonBareCentering

-- P0.06 exact negative control: cyclic trace axioms admit arbitrary constant real value, so genuine normalized SU(N) matrix trace bound must be sourced independently.
import DASHI.Physics.YangMills.YMClayOriginalPlaquetteTraceCyclicityInsufficientExact as OriginalPlaquetteTraceRangeNegativeControl

-- P0.06: source SU(N) matrix trace bound transports to every original cutoff plaquette and all finite Wilson words; explicit analytic source remains unpaid.
import DASHI.Physics.YangMills.YMClayE1D1OriginalSUNTraceToAllWordsBoundExact as OriginalSUNTraceAllWordBounds

-- P0 original R445 cross numerator: F*G is exactly original concatenated Wilson word, on actual signed plaquette source and Haar congruence.
import DASHI.Physics.YangMills.YMClayE1D1OriginalWilsonWordConcatenationR445Exact as OriginalWilsonWordConcatenation

-- P0.09 finite 2-point negative control: X(1)=0 and |F|<=1 do not force nonconstant RG error decay.
import DASHI.Physics.YangMills.YMClayE1D1CrossNumeratorCenteringDoesNotForceContractionExact as OriginalRGCrossNumeratorNonclosure

-- P0.01 independence control: the named scalar subtraction interaction fragment alone cannot prove x-0=x.
import DASHI.Physics.YangMills.YMClayRealSubtractionLawIndependenceExact as OriginalRealSubtractionNonclosure

-- E1/D1: genuine R445 original fine-vs-bare weighted cross numerator factors through selected normalized moment difference times BOTH source partitions (positive division remains explicit).
import DASHI.Physics.YangMills.YMClayE1D1OriginalCrossNumeratorNormalizedMomentFactorExact as OriginalRGNormalizedFactor

-- D2 negative control: one observed fast-decay transfer mode does not establish a gap on every non-vacuum mode.
import DASHI.Physics.YangMills.YMClayD2ObservedDecayDoesNotForceFullSpectralGapExact as OSObservableGapNegativeControl

-- P0 concrete scalar realization: pinned Murray/Csimma Bishop SETOID real proves subtraction, x-0, centered cancellation and positive inverse quotient law; does not identify with RealAnalysisAxioms abstract propositional ℝ.
import DASHI.Physics.YangMills.YMClayP0BishopRealCarrierInstancesExact as P0BishopRealArithmetic

-- P0 faithful source field weld: the actual Bishop setoid algebra derives original Wilson centering and division law records ONLY after a verified semantics-preserving original-real interpretation (still OPEN).
import DASHI.Physics.YangMills.YMClayP0BishopToOriginalWilsonRealWeldExact as P0OriginalBishopFieldWeld

-- P0.06 signed Wilson integration: actual original n=3 fine-blocked and independent n=1 bare Gibbs/Haar absolute expectation bounds from pointwise trace range and explicit ordered-real laws.
import DASHI.Physics.YangMills.YMClayE1D1OriginalSignedWilsonWordMomentBoundExact as OriginalSignedWilsonAbsoluteMomentBound

-- R443/R445: two original SU(N) links multiply to a Haar link (no Wilson interaction assumed).
import DASHI.Physics.YangMills.YMClaySUNOneLinkHaarConvolutionSourceExact as PureSUNHaarConvolution

-- R445 local kernel: explicit effective coarse density of any weighted two-link SU(N) Haar block, source-derived using exact group inverse, Haar left invariance, Fubini and scalar linearity.
import DASHI.Physics.YangMills.YMClaySUNTwoLinkHaarEffectiveFiberDensityExact as SUNHaarEffectiveFiberDensity
