module DASHI.Physics.Closure.NSClayFacingBResearchCutExact where

------------------------------------------------------------------------
-- CLAY-FACING B: TRUE MATHEMATICAL FRONTIER AFTER THE R236 RECUT
--
-- Keep the exact same-object Agda lane.  Standard finite algebra, rational
-- geometric summation, Bernstein, and already-proved low-output component
-- bounds are not research debt anymore.
--
-- 2026-10-04 MAX-CUT UPDATE
-- -------------------------
-- The live DFL-DFL, DFL-DHH and DHH-DHH blocks are reconstructed exactly as
-- literal unordered physical pair rows retaining their actual shell indices.
-- Those rows compile into the existing B1/B2/B3 payment records, so the leaf
-- producers no longer restate a live-block same-object equality.
--
-- B7 finite aggregation and exact endpoint/dynamic normal forms are already
-- available.  The attempted universal direct-companion = coherent-covariance
-- weld is rejected by the R289/R611 homogeneity audit (degree 5 vs degree 4).
-- A valid B7 producer must therefore close ONE of two analytic routes:
-- direct signed quintic spacetime payment, or quartic Gram+endpoint payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowFractionalShellPaymentExact as B1Legacy
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowLiteralInfinityShellPaymentExact as B1
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowDeepHHFractionalShellPaymentExact as B2
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepHHFractionalShellPaymentExact as B3
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingRelativeCovarianceExact as B4
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionAnalyticAssemblyExact as B5
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionUniformFamilyProducerExact as B6
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DecompositionExact as B7Legacy
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionLiteralPairExtractionMaxCutExact as Extract
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepBlocksFromLiteralRowsMaxCutExact as RowCompiler
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DirectCompanionMaxCutExact as B7Direct
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406HomogeneityBoundaryMaxCutExact as B7Boundary
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406ProducerChoiceMaxCutExact as B7Producer
import DASHI.Physics.Closure.NSTriadKNDeepFarLowDyadicBernsteinWeldRound466Exact as R466
import DASHI.Physics.Closure.NSTriadKNHeterochiralHHGapEnvelopeRound136Exact as R136
import DASHI.Physics.Closure.NSTriadKNR106ComponentLowOutputBoundRound574Exact as R574
import DASHI.Physics.Closure.NSPeriodicInfinityShellSubsetCountExact as ShellSubset
import DASHI.Physics.Closure.NSTriadKNLiteralInfinityShellBernsteinPaymentExact as LiteralShell

data BResidual : Set where
  literalDFLFilteredBlockToShellData : BResidual
  literalDFLDHHPerShellSignedEstimate : BResidual
  literalDHHIntraShellSignedL2 : BResidual
  strictCriticalSignedOperator : BResidual
  literalR406SameObjectEquality : BResidual
  oneValidR406Producer : BResidual
  terminalCompilerOnly : BResidual

boolOr : Bool → Bool → Bool
boolOr true _ = true
boolOr false b = b

------------------------------------------------------------------------
-- Already-paid analytic / representation ingredients.
------------------------------------------------------------------------

bR466FiniteBernsteinCompilerClosed : Bool
bR466FiniteBernsteinCompilerClosed = R466.round466DeepFarLowDyadicCompilerClosed

bLiteralInfinityShellSubsetCountClosed : Bool
bLiteralInfinityShellSubsetCountClosed = ShellSubset.literalInfinityShellSubsetCountClosed

bLiteralInfinityShellBernsteinCompilerClosed : Bool
bLiteralInfinityShellBernsteinCompilerClosed = LiteralShell.literalInfinityShellBernsteinCompilerClosed

bB1StillRequiresSyntheticEightfoldCarrier : Bool
bB1StillRequiresSyntheticEightfoldCarrier = B1.deepFarLowLiteralInfinityShellFoldUsesSyntheticEightfoldCarrier

bHHGapSummationClosed : Bool
bHHGapSummationClosed = R136.round136HHGapIndexSummationClosed

bFourComponentLowOutputBoundClosed : Bool
bFourComponentLowOutputBoundClosed = R574.round574AllFourPhysicalHelicalComponentsHaveLowOutputBound

bB1CanonicalShellSupportClosed : Bool
bB1CanonicalShellSupportClosed = B1.deepFarLowLiteralInfinityShellSupportChoiceClosed

bB1ShellFoldCompilerClosed : Bool
bB1ShellFoldCompilerClosed = B1.deepFarLowLiteralInfinityShellFoldCompilerClosed

bB2BipartiteFoldCompilerClosed : Bool
bB2BipartiteFoldCompilerClosed = B2.deepFarLowDeepHHBipartiteShellFoldClosed

bB3ShellFoldCompilerClosed : Bool
bB3ShellFoldCompilerClosed = B3.deepHHShellFoldClosed

bB4SignedOperatorCompilerClosed : Bool
bB4SignedOperatorCompilerClosed = B4.criticalTouchingSignedBlockOperatorCompilerClosed

bB5PhysicalPaymentAssemblyClosed : Bool
bB5PhysicalPaymentAssemblyClosed = B5.fixedOutputB1B4ToPhysicalPaymentCompilerClosed

bB6UniformFamilyCompilerClosed : Bool
bB6UniformFamilyCompilerClosed = B6.uniformPhysicalCriticalRegionFamilyCompilerClosed

bB7R406DecompositionCompilerClosed : Bool
bB7R406DecompositionCompilerClosed = B7Legacy.criticalRegionR406DecompositionCompilerClosed

bLiteralDeepPairExtractionClosed : Bool
bLiteralDeepPairExtractionClosed = Extract.b1LiteralDFLPairExtractionClosed

bLiteralDFLDHHPairExtractionClosed : Bool
bLiteralDFLDHHPairExtractionClosed = Extract.b2LiteralDFLDHHPairExtractionClosed

bLiteralDHHPairExtractionClosed : Bool
bLiteralDHHPairExtractionClosed = Extract.b3LiteralDHHPairExtractionClosed

bB1B3LiveBlockSameObjectFieldsCompiledFromRows : Bool
bB1B3LiveBlockSameObjectFieldsCompiledFromRows = RowCompiler.b1B3LiveBlockSameObjectFieldsCompiledFromRows

bR406GlobalFiniteAggregationClosed : Bool
bR406GlobalFiniteAggregationClosed = B7Direct.b7R406GlobalAggregationClosed

bR406UniversalCovarianceEqualityAdmissible : Bool
bR406UniversalCovarianceEqualityAdmissible = B7Boundary.b7UniversalDirectCompanionCovarianceEqualityAdmissible

bR406ExactEndpointNormalFormCompilerClosed : Bool
bR406ExactEndpointNormalFormCompilerClosed = B7Producer.b7ExactEndpointNormalFormCompilerClosed

bR406QuarticGramEndpointCompilerAvailable : Bool
bR406QuarticGramEndpointCompilerAvailable = B7Producer.b7QuarticGramEndpointCompilerAvailable

------------------------------------------------------------------------
-- Genuine remaining inhabitants.
------------------------------------------------------------------------

bDFLPhysicalShellExtractionClosed : Bool
bDFLPhysicalShellExtractionClosed = B1.deepFarLowLiteralInfinityShellPhysicalExtractorInhabitedHere

bDFLDHHPerShellSignedEstimateClosed : Bool
bDFLDHHPerShellSignedEstimateClosed = B2.deepFarLowDeepHHPerShellNullBernsteinEstimateInhabitedHere

bDHHIntraShellSignedL2Closed : Bool
bDHHIntraShellSignedL2Closed = B3.deepHHIntraShellSignedL2AggregationInhabitedHere

bCriticalStrictSignedOperatorClosed : Bool
bCriticalStrictSignedOperatorClosed = B4.criticalTouchingStrictOperatorCertificateInhabitedHere

bLegacyLiteralR406CovarianceEqualityClosed : Bool
bLegacyLiteralR406CovarianceEqualityClosed = B7Legacy.literalR406SameObjectEqualityInhabitedHere

bR406DirectSignedQuinticRouteClosed : Bool
bR406DirectSignedQuinticRouteClosed = B7Producer.b7DirectSignedQuinticRouteClosed

bR406QuarticGramEndpointRouteClosed : Bool
bR406QuarticGramEndpointRouteClosed = B7Producer.b7QuarticGramEndpointRouteClosed

bR406OneProducerRouteClosed : Bool
bR406OneProducerRouteClosed = boolOr bR406DirectSignedQuinticRouteClosed bR406QuarticGramEndpointRouteClosed

/-- Compatibility name for older consumers: the active B7 requirement is now
one valid producer route, not a universal same-object equality. -/
bLiteralR406SameObjectClosed : Bool
bLiteralR406SameObjectClosed = bR406OneProducerRouteClosed

bR406DynamicTransportClosed : Bool
bR406DynamicTransportClosed = bR406OneProducerRouteClosed

currentBResidual : BResidual
currentBResidual = literalDFLFilteredBlockToShellData

bHighestInformationWallIsStrictCriticalOperator : Bool
bHighestInformationWallIsStrictCriticalOperator = true

bGenericAnalysisReimplementationRequired : Bool
bGenericAnalysisReimplementationRequired = false

bShouldMigrateToLean : Bool
bShouldMigrateToLean = false

bKeepExactSameObjectAgdaLane : Bool
bKeepExactSameObjectAgdaLane = true

------------------------------------------------------------------------
-- Receipts.
------------------------------------------------------------------------

bLiteralDeepPairExtractionClosedIsTrue : bLiteralDeepPairExtractionClosed ≡ true
bLiteralDeepPairExtractionClosedIsTrue = refl

bB1B3LiveBlockSameObjectFieldsCompiledFromRowsIsTrue :
  bB1B3LiveBlockSameObjectFieldsCompiledFromRows ≡ true
bB1B3LiveBlockSameObjectFieldsCompiledFromRowsIsTrue = refl

bR406GlobalFiniteAggregationClosedIsTrue : bR406GlobalFiniteAggregationClosed ≡ true
bR406GlobalFiniteAggregationClosedIsTrue = refl

bR406UniversalCovarianceEqualityAdmissibleIsFalse :
  bR406UniversalCovarianceEqualityAdmissible ≡ false
bR406UniversalCovarianceEqualityAdmissibleIsFalse = refl

bR406ExactEndpointNormalFormCompilerClosedIsTrue :
  bR406ExactEndpointNormalFormCompilerClosed ≡ true
bR406ExactEndpointNormalFormCompilerClosedIsTrue = refl

bR406QuarticGramEndpointCompilerAvailableIsTrue :
  bR406QuarticGramEndpointCompilerAvailable ≡ true
bR406QuarticGramEndpointCompilerAvailableIsTrue = refl

bR406DirectSignedQuinticRouteClosedIsFalse : bR406DirectSignedQuinticRouteClosed ≡ false
bR406DirectSignedQuinticRouteClosedIsFalse = refl

bR406QuarticGramEndpointRouteClosedIsFalse : bR406QuarticGramEndpointRouteClosed ≡ false
bR406QuarticGramEndpointRouteClosedIsFalse = refl

bR406OneProducerRouteClosedIsFalse : bR406OneProducerRouteClosed ≡ false
bR406OneProducerRouteClosedIsFalse = refl

bGenericAnalysisReimplementationRequiredIsFalse : bGenericAnalysisReimplementationRequired ≡ false
bGenericAnalysisReimplementationRequiredIsFalse = refl

bShouldMigrateToLeanIsFalse : bShouldMigrateToLean ≡ false
bShouldMigrateToLeanIsFalse = refl

bKeepExactSameObjectAgdaLaneIsTrue : bKeepExactSameObjectAgdaLane ≡ true
bKeepExactSameObjectAgdaLaneIsTrue = refl
