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
