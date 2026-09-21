module DASHI.Physics.Closure.NSClayFacingBResearchCutExact where

------------------------------------------------------------------------
-- CLAY-FACING B: TRUE MATHEMATICAL FRONTIER AFTER THE R236 RECUT
--
-- Keep the exact same-object Agda lane.  Standard finite algebra, rational
-- geometric summation, Bernstein, and already-proved low-output component
-- bounds are not research debt anymore.  The remaining proof-critical work is
-- the literal physical extraction/aggregation needed to apply them without
-- losing signed cancellation, plus the strict critical operator estimate and
-- the final R406 same-object identity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowFractionalShellPaymentExact as B1
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowDeepHHFractionalShellPaymentExact as B2
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepHHFractionalShellPaymentExact as B3
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingRelativeCovarianceExact as B4
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionAnalyticAssemblyExact as B5
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionUniformFamilyProducerExact as B6
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DecompositionExact as B7
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
  terminalCompilerOnly : BResidual

------------------------------------------------------------------------
-- Already-paid analytic ingredients.
------------------------------------------------------------------------

bR466FiniteBernsteinCompilerClosed : Bool
bR466FiniteBernsteinCompilerClosed = R466.round466DeepFarLowDyadicCompilerClosed

bLiteralInfinityShellSubsetCountClosed : Bool
bLiteralInfinityShellSubsetCountClosed =
  ShellSubset.literalInfinityShellSubsetCountClosed

bLiteralInfinityShellBernsteinCompilerClosed : Bool
bLiteralInfinityShellBernsteinCompilerClosed =
  LiteralShell.literalInfinityShellBernsteinCompilerClosed

bB1StillRequiresSyntheticEightfoldCarrier : Bool
bB1StillRequiresSyntheticEightfoldCarrier =
  LiteralShell.literalInfinityShellUsesSyntheticEightfoldCarrier

bHHGapSummationClosed : Bool
bHHGapSummationClosed = R136.round136HHGapIndexSummationClosed

bFourComponentLowOutputBoundClosed : Bool
bFourComponentLowOutputBoundClosed =
  R574.round574AllFourPhysicalHelicalComponentsHaveLowOutputBound

bB1ShellFoldCompilerClosed : Bool
bB1ShellFoldCompilerClosed = B1.deepFarLowShellFoldCompilerClosed

bB2BipartiteFoldCompilerClosed : Bool
bB2BipartiteFoldCompilerClosed =
  B2.deepFarLowDeepHHBipartiteShellFoldClosed

bB3ShellFoldCompilerClosed : Bool
bB3ShellFoldCompilerClosed = B3.deepHHShellFoldClosed

bB4SignedOperatorCompilerClosed : Bool
bB4SignedOperatorCompilerClosed =
  B4.criticalTouchingSignedBlockOperatorCompilerClosed

bB5PhysicalPaymentAssemblyClosed : Bool
bB5PhysicalPaymentAssemblyClosed =
  B5.fixedOutputB1B4ToPhysicalPaymentCompilerClosed

bB6UniformFamilyCompilerClosed : Bool
bB6UniformFamilyCompilerClosed =
  B6.uniformPhysicalCriticalRegionFamilyCompilerClosed

bB7R406DecompositionCompilerClosed : Bool
bB7R406DecompositionCompilerClosed =
  B7.criticalRegionR406DecompositionCompilerClosed

------------------------------------------------------------------------
-- Genuine remaining inhabitants.
------------------------------------------------------------------------

bDFLPhysicalShellExtractionClosed : Bool
bDFLPhysicalShellExtractionClosed =
  B1.deepFarLowLiteralFilteredBlockShellExtractorInhabitedHere

bDFLDHHPerShellSignedEstimateClosed : Bool
bDFLDHHPerShellSignedEstimateClosed =
  B2.deepFarLowDeepHHPerShellNullBernsteinEstimateInhabitedHere

bDHHIntraShellSignedL2Closed : Bool
bDHHIntraShellSignedL2Closed =
  B3.deepHHIntraShellSignedL2AggregationInhabitedHere

bCriticalStrictSignedOperatorClosed : Bool
bCriticalStrictSignedOperatorClosed =
  B4.criticalTouchingStrictOperatorCertificateInhabitedHere

bLiteralR406SameObjectClosed : Bool
bLiteralR406SameObjectClosed =
  B7.literalR406SameObjectEqualityInhabitedHere

currentBResidual : BResidual
currentBResidual = literalDFLFilteredBlockToShellData

bGenericAnalysisReimplementationRequired : Bool
bGenericAnalysisReimplementationRequired = false

bShouldMigrateToLean : Bool
bShouldMigrateToLean = false

bKeepExactSameObjectAgdaLane : Bool
bKeepExactSameObjectAgdaLane = true

bGenericAnalysisReimplementationRequiredIsFalse :
  bGenericAnalysisReimplementationRequired ≡ false
bGenericAnalysisReimplementationRequiredIsFalse = refl

bShouldMigrateToLeanIsFalse : bShouldMigrateToLean ≡ false
bShouldMigrateToLeanIsFalse = refl

bKeepExactSameObjectAgdaLaneIsTrue :
  bKeepExactSameObjectAgdaLane ≡ true
bKeepExactSameObjectAgdaLaneIsTrue = refl
