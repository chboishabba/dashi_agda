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
-- Canonical 1024-link marked tests -> actual 64 blocked holonomies ->
-- physical F19 effective measure, including same-original-Z normalization.
-- Source-written; legacy scalar and compact Haar remain explicit inputs.
import DASHI.Physics.YangMills.YMClayOriginalWilsonCanonicalBlockedMarkF19Exact as CanonicalBlockedF19
import DASHI.Physics.YangMills.YMClayP0FGeneratedTwoSourceInteractionNegativeControlExact as P0FGeneratedInteractionNegativeControl

import DASHI.Physics.YangMills.YMClayNativeR445TemporalReversalExact as NativeTimeReflection

-- P0 BIDI same original native SU(N) source: R445 even-time reflected
-- bond fields, original finite plaquette words, and the exact centered
-- original n=3 Wilson mixed-J == actual R320 reflected-covariance seam.
-- Physical time, CMP116 uniform-rate estimate and OS mass gap remain open.
import DASHI.Physics.YangMills.YMClayR445SelectedTimeReflectionForwardExact as NativeSelectedTimeReflection
import DASHI.Physics.YangMills.YMClayOriginalR445ReflectedPointwiseWordWeldExact as NativeWordPointwiseReflection
import DASHI.Physics.YangMills.YMClayOriginalR445ReflectedWordCMP116BIDIExact as OriginalReflectedWordBIDI

-- P0 forward/reverse SAME ALL-TIME original Wilson carrier: one Nat-indexed
-- translated family instead of per-time singleton, R556/R278/R551 + R281,
-- and R332 original OS1 time plus R304 physical shell-distance identification.
-- The physical WEXT, scalar ℚ↔original ℝ, same-H and E1 are still open.
import DASHI.Physics.YangMills.YMClayOriginalWilsonAllTimesOS1R556R281BIDIExact as OriginalAllTimesOS1Weld

-- Correct original WEXT source geometry and W1/W3->OS1->R556->R551->R281 producer route.
-- The old arbitrary-metric time axiom was vacuous; its safe negative control
-- and both corrected original source consumers are imported here.
import DASHI.Physics.YangMills.YMClayWilsonWEXTSelectedDistanceNonVacuityExact as OriginalWEXTNonVacuity
import DASHI.Physics.YangMills.BalabanLiteralWilsonMarkedLocalizationSourceExact as OriginalMarkedWEXT
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonR556CompletionExact as OriginalTwiceWilsonWEXT
import DASHI.Physics.YangMills.YMClayOriginalWilsonMarkedOS1AllTimesProducerWeldExact as OriginalMarkedOS1BIDI

-- Explicit BIDI same-source square: R556 source vs OS1 translation
-- commutes on each original finite and continuum R278 covariance,
-- and closes at one R281 indexed spectrum (not physical H_OS yet).
import DASHI.Physics.YangMills.YMClayOriginalWilsonOS1R556R281CommutingSquareExact as OriginalOS1CovarianceSquare

-- Canonical SI/metrology source WELD at actual original two-link R445
-- block: fine spacing [m], native pair length [m], and (under explicit
-- coarse inverse-spacing calibration) same inverse correlation length
-- [m^-1]. Existing SI YangMills scaling owns kg/J conversion. This
-- contains NO inferred W1/W3 physical rate or continuous spectrum proof.
import DASHI.Physics.YangMills.YMClayR445Base2SIPhysicalRateBIDIExact as OriginalR445SIPhysicalRate

-- Source-written original R445 fine PositiveBond4 <-> (original 64-coarse
-- bond, two-link axial phase, three transverse parity bits).  Entire
-- 1024-bond source partitions into 8 reversible 128-bond binary sheets:
-- selected residual 000 = original R445 128; seven others = original 896.
-- This uses EXISTING Base369 2^a*3^b and signed-bit donors; binary 000
-- is the signed corner (-,-,-), NOT the balanced ternary zero fibre.
-- No Wilson action symmetry, missing Gibbs estimate or Agda receipt claimed.
import DASHI.Physics.YangMills.YMClayR445Base2ThreeAxis369FibreBIDIExact as OriginalR445Base2ThreeAxis369

-- P0 original t × k residual HYPERFABRIC: native R445 C4 split into
-- source-owned C2 coarse × parity remainder, original 128+896 bond
-- complete enumeration, exact odd-step carry and independent ternary
-- zero/sign wave symbol. This is NOT a physical continuum limit.
import DASHI.Physics.YangMills.YMClayR445TimeKResidualHyperfabricExact as OriginalTimeKResidual

-- Original E1 actual cutoff-dependent Wilson cylinders: k indexes the
-- selected Nat-cutoff family; split/join preserves all residuals at
-- suc k; original E1 convergence is reused WITHOUT assuming arbitrary
-- Converges is shift/tail-invariant. OS1 time source identity remains input.
import DASHI.Physics.YangMills.YMClayE1TimeKResidualCylinderWaveTransportExact as OriginalTimeKE1

-- P0 original *already-normalized* full Wilson F19 source:
-- F,G,FG under same original 1024-link partition (896 spectators)
-- imply the entire exact finite connected covariance on the canonical
-- source equals F19 physical effective density. No bare-coarse switch.
import DASHI.Physics.YangMills.YMClayOriginalF19CanonicalConnectedWilsonBIDIExact as OriginalF19Connected

-- F19 and native R445 first/second positive-bond selected target lists
-- are the SAME original 128 bonds in the SAME canonical pair order;
-- this is by original native first/second parity proof, not an arbitrary
-- vector bijection, prior to comparing the remaining 896 spectators.
import DASHI.Physics.YangMills.YMClayOriginalF19R445Full1024LabelsP0Exact as OriginalFullF19R445Labels
-- Once the original F19 1024-label target is proved, its SAME
-- original native constructed adjacent-swap permutation agrees on
-- every arbitrary SU(N) link value with original R445 complete codec.
-- All 896 original interacting spectators remain present.
import DASHI.Physics.YangMills.YMClayOriginalF19R445EveryLinkValueBIDIExact as OriginalF19R445Values
import DASHI.Physics.YangMills.YMClayOriginalF19R445ActualSortedVectorBIDIExact as OriginalF19R445SortSquare

-- Actual finite decoder commuting square (all 1024 original bonds):
-- canonical field --original F19 adjacent swap--> selected128+residual896
--       |                                            |
-- original canonical decoder                   original R445 decoder
--       |                                            |
-- original bond field ----------------identity--> original bond field.
-- Also both original inverse vector round-trips. Not a physical OS square.
import DASHI.Physics.YangMills.YMClayOriginalF19R445DecoderCommutingSquareExact as OriginalF19R445DecoderSquare

-- Separate physical finite BLOCKED-observable square: same original
-- Wilson 64-pair holonomies, through actual F19 adjacent sort or
-- the full original R445 128+896 ordered field coordinates.
-- Distinct from unproved E1/D1/D2 continuum mass-gap obligation.
import DASHI.Physics.YangMills.YMClayOriginalF19R445PhysicalBlockedObservableSquareExact as OriginalF19R445BlockedObservableSquare

-- Native source-equality payment: original constructed F19 64 pair-block
-- and ORIGINAL native R445 SUNBlock.nativeSUNBlockLinks at each of the
-- 64 original coarse bonds, source parity and genuine 1024-link decoder.
-- Source-written closed 64-order computation requires pinned Agda kernel.
import DASHI.Physics.YangMills.YMClayOriginalF19R445Native64HolonomySquareExact as OriginalF19NativeR445Square

-- P0 directly instantiates the ALREADY ORIGINAL R445 two-field pure-Haar
-- receiver using F19 adjacent swaps and native 64-block source candidates.
-- Distinguish unweighted Haar from interacting Wilson Gibbs 896 spectators.
-- SymPy exact finite checks PASS; Agda kernel still NOT run.
import DASHI.Physics.YangMills.YMClayOriginalF19R445PureHaarReceiverCandidateExact as OriginalF19NativePureHaarCandidate

-- Reverse physical Wilson E1 native cutoff-3 expectation, weld FORWARD
-- from ORIGINAL complete 1024-link Gibbs F19 weighted effective density.
-- Do not infer the interacting Wilson source from unweighted pure-Haar.
import DASHI.Physics.YangMills.YMClayOriginalR445NativeF19WeightedPhysicalSourceBIDIExact as OriginalNativeWeightedF19BIDI

-- E1 cutoff-3 physical source is already the SAME original n=3
-- native Wilson Gibbs R445 pushforward. Composes original F19 weighted
-- all-observable source with E1A3, then the same E1/R445 F,G,FG
-- three-moment covariance error. Genuine analytic uniformity OPEN.
import DASHI.Physics.YangMills.YMClayOriginalE1A3NativeF19WeightedBIDIExact as OriginalE1F19ThreeMomentBIDI

-- Use ORIGINAL D1 full SU(N) Wilson small+large-field cutoff-uniform
-- covariance theorem. Source-selection demands only pointwise identity
-- of chosen D1 tests with actual E1/native R445 block F,G; never
-- restate or postulate the covariance bound or discard large fields.
-- Fixed cutoff3 F19 face; all-scale physical rates still require a
-- source-inhabited OriginalSmallLargePhysicalSource and time geometry.
import DASHI.Physics.YangMills.YMClayOriginalD1FullWilsonE1F19EstimateBIDIExact as OriginalD1F19UniformWeld
import DASHI.Physics.YangMills.YMClayOriginalF19NativeR445SelectedOrderBIDIExact as OriginalF19R445SelectedOrder

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

-- R443/R445 all finite n native SU(N) Haar-paired product block, including 64-coarse/896-unused cardinality specialization; original bond codec identification still OPEN.
import DASHI.Physics.YangMills.YMClaySUNFinitePairedHaarBlockPushforwardExact as NativeFinitePairedSUNHaar

-- Original 4->2 periodic positive-bond parity/index and native holonomy weld; source candidate, Agda check pending.
import DASHI.Physics.YangMills.YMClayR445OriginalAxialBondParityInjectiveExact as R445OriginalAxialParity

-- Original 4->2 periodic positive-bond parity/index and native holonomy weld; source candidate, Agda check pending.
import DASHI.Physics.YangMills.YMClayR445NativePairHolonomyIdentityExact as R445NativePairHolonomy

-- Original 4->2 periodic positive-bond parity/index and native holonomy weld; source candidate, Agda check pending.
import DASHI.Physics.YangMills.YMClayR445OriginalNativeParityPairWeldExact as R445NativeParityWeld

-- P0.B: explicit canonical side-four 1024-bond list -> 128 selected pair bonds and 896 residual bonds, source finite enumeration, disjoint/completeness and Vec codec round trips; local checker pending.
import DASHI.Physics.YangMills.YMClayR445CanonicalBondPermutationCodecExact as R445CanonicalPairResidualCodec

-- P0.D: true flat SU(N) 2n+m product-Haar -> n pair products plus m discarded Haar links, 1024-to-64 source cardinalities; final canonical reorder witness remains OPEN.
import DASHI.Physics.YangMills.YMClayR445FlatPairedHaarIntegrationExact as R445FlatHaarBlock

-- P0.D original-native pure Haar blocking: full formal implication from concrete canonical permutation word and native coarse-vector order equality to actual original n=3->n=1 product Haar. Both weld certificates remain explicit/uninhabited.
import DASHI.Physics.YangMills.YMClayR445OriginalPureHaarBlockWeldExact as R445OriginalPureHaarWeld

-- P0.E: actual original side-four interacting Wilson action expressed in exact 64 coarse/64 relative/896 interior source coordinates; pointwise/partition positive; physical weighted canonical pushforward equality and UV decay still OPEN.
import DASHI.Physics.YangMills.YMClayR445OriginalFullWilsonFiberDensityExact as R445OriginalFullWilsonFibers

-- P0.D supporting typed finite adjacent-swap schedule compiler. The preferred already-source-written original 1024-label permutation owner is NativeClosedThreeEqualities/M01; both require local kernel acceptance.
import DASHI.Physics.YangMills.YMClayR445AdjacentHaarPermutationCompilerExact as AdjacentHaarSchedule
