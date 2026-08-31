module DASHI.Cognition.PNF.SensibLawRuntimeNumericProjectionBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.BinaryBalancedTernaryAggregateLossExact as BinaryTernary
import DASHI.Cognition.PNF.SensibLawGWBv01RuntimeCertificationExact as GWB
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- Runtime numeric projection boundary.
--
-- The GWB receipt has a fine timing carrier.  Gate and tier labels are valid
-- consumer projections of that carrier; they are not reconstructions of it.
------------------------------------------------------------------------

record RuntimePerformanceProjection : Set where
  constructor runtime-performance-projection
  field
    gatePassed : Bool
    tier : GWB.MeasuredPerformanceTier

open RuntimePerformanceProjection public

gwbV01PerformanceProjection : RuntimePerformanceProjection
gwbV01PerformanceProjection =
  runtime-performance-projection
    (GWB.fullGatePassed GWB.gwbV01CertifiedRun)
    (GWB.measuredTier GWB.gwbV01Timing)

------------------------------------------------------------------------
-- A finite non-factorability witness: two distinct fine timing states can have
-- the same gate/tier projection.
------------------------------------------------------------------------

data TimingFixture : Set where
  parserDominatedA parserDominatedB : TimingFixture

projection : TimingFixture → RuntimePerformanceProjection
projection parserDominatedA =
  runtime-performance-projection true GWB.production1_2x
projection parserDominatedB =
  runtime-performance-projection true GWB.production1_2x

data ActiveWorkClass : Set where
  lowerActiveWork higherActiveWork : ActiveWorkClass

activeWorkClass : TimingFixture → ActiveWorkClass
activeWorkClass parserDominatedA = lowerActiveWork
activeWorkClass parserDominatedB = higherActiveWork

sameProjection :
  projection parserDominatedA ≡ projection parserDominatedB
sameProjection = refl

activeWorkStillDiffers :
  activeWorkClass parserDominatedA ≡ activeWorkClass parserDominatedB → ⊥
activeWorkStillDiffers ()

performanceProjectionCannotRecoverFineTiming :
  INF.FactorsThrough projection activeWorkClass → ⊥
performanceProjectionCannotRecoverFineTiming =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      parserDominatedA
      parserDominatedB
      sameProjection
      activeWorkStillDiffers)

------------------------------------------------------------------------
-- Exact GWB timing coordinates remain first-class.
------------------------------------------------------------------------

gwbModelColdLoadNs : Nat
gwbModelColdLoadNs = GWB.spacyModelColdLoadNs GWB.gwbV01Timing

gwbParserOccupancyNs : Nat
gwbParserOccupancyNs = GWB.spacyParserWallOccupancyNs GWB.gwbV01Timing

gwbSensibLawActiveNs : Nat
gwbSensibLawActiveNs = GWB.sensibLawActiveNs GWB.gwbV01Timing

gwbTotalPipelineWallNs : Nat
gwbTotalPipelineWallNs = GWB.totalSemanticPipelineWallNs GWB.gwbV01Timing

gwbControllerWallNs : Nat
gwbControllerWallNs = GWB.externalControllerWallNs GWB.gwbV01Timing

gwbPostParserTailNs : Nat
gwbPostParserTailNs = GWB.postParserTailNs GWB.gwbV01Timing

------------------------------------------------------------------------
-- Cross-pollination with the merged binary/balanced-ternary owner.
--
-- That owner already proves that a declared Boolean projection remains useful
-- while a later aggregate can erase disagreement direction.  SensibLaw adopts
-- the same discipline: changing the codomain from Bool to a three-way tier does
-- not by itself restore the fine runtime carrier.
------------------------------------------------------------------------

binaryAggregateCanEraseDirection :
  BinaryTernary.acceptCount
    (BinaryTernary.binaryProjectPositiveOnly BinaryTernary.forwardDisagreement)
  ≡ BinaryTernary.acceptCount
    (BinaryTernary.binaryProjectPositiveOnly BinaryTernary.reverseDisagreement)
binaryAggregateCanEraseDirection =
  BinaryTernary.aggregateErasesDisagreementDirection

------------------------------------------------------------------------
-- Hard no-collapse / no-authority boundaries.
------------------------------------------------------------------------

data GatePassIsCompleteRuntimeSemantics : Set where
data ThreeWayTierIsCompleteRuntimeSemantics : Set where
data PerformanceProjectionPromotesSemanticTruth : Set where
data SameTierMeansSameTimingDecomposition : Set where

gatePassDoesNotCompleteRuntimeSemantics :
  GatePassIsCompleteRuntimeSemantics → ⊥
gatePassDoesNotCompleteRuntimeSemantics ()

threeWayTierDoesNotCompleteRuntimeSemantics :
  ThreeWayTierIsCompleteRuntimeSemantics → ⊥
threeWayTierDoesNotCompleteRuntimeSemantics ()

performanceProjectionStillCannotPromoteSemanticTruth :
  PerformanceProjectionPromotesSemanticTruth → ⊥
performanceProjectionStillCannotPromoteSemanticTruth ()

sameTierDoesNotMeanSameTimingDecomposition :
  SameTierMeansSameTimingDecomposition → ⊥
sameTierDoesNotMeanSameTimingDecomposition ()

record SensibLawRuntimeNumericProjectionBoundary : Set where
  constructor sensiblaw-runtime-numeric-projection-boundary
  field
    fineTimingVectorRetained : Bool
    booleanGateIsDeclaredProjection : Bool
    threeWayTierIsDeclaredProjection : Bool
    sameProjectionCanHideDifferentFineTiming : Bool
    binaryOrTernaryCodeReconstructsFineCarrier : Bool
    performanceCodeHasSemanticAuthority : Bool

canonicalSensibLawRuntimeNumericProjectionBoundary :
  SensibLawRuntimeNumericProjectionBoundary
canonicalSensibLawRuntimeNumericProjectionBoundary =
  sensiblaw-runtime-numeric-projection-boundary
    true true true true false false
