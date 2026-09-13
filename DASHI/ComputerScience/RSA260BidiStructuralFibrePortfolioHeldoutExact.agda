module DASHI.ComputerScience.RSA260BidiStructuralFibrePortfolioHeldoutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiTwoHopCommonNeighbourFibreExact as TwoHop
import DASHI.ComputerScience.RSA260BidiFineIncidenceDefectCoverageExact as Coverage
import DASHI.ComputerScience.RSA260BidiKrylovReachableRankExact as DynamicRank

------------------------------------------------------------------------
-- HELD-OUT STRUCTURAL-FIBRE PORTFOLIO
--
-- Fit recurrence complexity from repo-native static structural fibres:
-- row/column common-neighbour means/std/entropy, adjacent and distance-two
-- overlaps, and profile-step L1 variation.
--
-- Training: 18 carriers from three perturbation seeds x six coverage levels.
-- Held out: independent perturbation seed 271011 at six coverage levels.
--
-- Result:
--   held-out MAE ~= 2.328871 generator degrees.
--
-- Surviving counterexample:
--   touched rows = 256
--   observed d = 64
--   predicted d ~= 56.8277
--   absolute residual ~= 7.1723.
--
-- The residual is retained as a repair obligation.  The dynamic reachable-rank
-- owner is the current candidate missing fibre; this owner does not silently
-- insert it into the already-evaluated static predictor.
------------------------------------------------------------------------

twoHopBoundary : TwoHop.TwoHopInterpretationBoundary
twoHopBoundary = TwoHop.canonicalTwoHopInterpretationBoundary

coverageBoundary : Coverage.DefectCoverageInterpretationBoundary
coverageBoundary = Coverage.canonicalDefectCoverageInterpretationBoundary

dynamicRankBoundary : DynamicRank.DynamicRankInterpretationBoundary
dynamicRankBoundary = DynamicRank.canonicalDynamicRankInterpretationBoundary

record StructuralPortfolioRuntimeSource : Set where
  constructor structural-portfolio-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    directDependencyPath : String
    directDependencyGitBlob : String
    exactTopLevelBlobExecuted : Bool
    exactDirectDependencyBlobBound : Bool
open StructuralPortfolioRuntimeSource public

currentStructuralPortfolioRuntimeSource : StructuralPortfolioRuntimeSource
currentStructuralPortfolioRuntimeSource = structural-portfolio-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_structural_portfolio_heldout.py"
  "599886ead3413cebe8746db98ce76c37af1be31c"
  "f8f2bbe42d0cb3ef947a344e2996e93afae41e56"
  "rsa260_bidi_fine_incidence_defect_coverage.py"
  "777b261b7d76095b04a1ea2ae574439cd9d63144"
  true true

record StructuralPortfolioHeldoutReceipt : Set where
  constructor structural-portfolio-heldout-receipt
  field
    structuralFibreCount : Nat
    trainingPoints : Nat
    heldoutCoverageLevels : Nat
    heldoutSeed : Nat
    ridgeLambdaLabel : String
    heldoutMAELabel : String
    allHeldoutConsumersRecovered : Bool
    largestResidualTouchedRows : Nat
    largestResidualObservedDegree : Nat
    largestResidualPredictedDegreeLabel : String
    largestResidualAbsoluteErrorLabel : String
open StructuralPortfolioHeldoutReceipt public

currentStructuralPortfolioHeldoutReceipt : StructuralPortfolioHeldoutReceipt
currentStructuralPortfolioHeldoutReceipt = structural-portfolio-heldout-receipt
  12
  18
  6
  271011
  "0.3"
  "2.328871159849383"
  true
  256
  64
  "56.82772330817217"
  "7.1722766918278325"

record StructuralPortfolioInterpretationBoundary : Set where
  constructor structural-portfolio-interpretation-boundary
  field
    staticStructuralPortfolioHasHeldoutPredictiveSignal : Bool
    staticStructuralPortfolioExactlyPredictsGeneratorDegree : Bool
    largestResidualRetainedAsCounterexample : Bool
    reachableKrylovRankIsCandidateRepairFibre : Bool
    dynamicRankAlreadyIncludedInStaticFit : Bool
    heldoutFitIsCausalMechanismProof : Bool
    heldoutFitIsProductionMeasurement : Bool
open StructuralPortfolioInterpretationBoundary public

canonicalStructuralPortfolioInterpretationBoundary : StructuralPortfolioInterpretationBoundary
canonicalStructuralPortfolioInterpretationBoundary = structural-portfolio-interpretation-boundary
  true
  false
  true
  true
  false
  false
  false

data StructuralPortfolioResidual : Set where
  addReachableKrylovRankAsRepairFibre : StructuralPortfolioResidual
  rerunHeldoutPredictionAfterDynamicRepair : StructuralPortfolioResidual
  crossValidateDynamicRepairAcrossPreparationFibres : StructuralPortfolioResidual
  measurePortfolioOnSameObjectProductionArtifacts : StructuralPortfolioResidual

firstStructuralPortfolioResidual : StructuralPortfolioResidual
firstStructuralPortfolioResidual = addReachableKrylovRankAsRepairFibre

data GoodHeldoutMAEImpliesExactPredictor : Set where
data StaticCorrelationImpliesCausalMechanism : Set where
data SyntheticPredictorImpliesProductionMeasurement : Set where
data CounterexampleMayBeDiscardedAfterAverageFit : Set where

goodMAEDoesNotCreateExactPredictor : GoodHeldoutMAEImpliesExactPredictor → ⊥
goodMAEDoesNotCreateExactPredictor ()

staticCorrelationDoesNotCreateCausalMechanism : StaticCorrelationImpliesCausalMechanism → ⊥
staticCorrelationDoesNotCreateCausalMechanism ()

syntheticPredictorDoesNotCreateProductionMeasurement : SyntheticPredictorImpliesProductionMeasurement → ⊥
syntheticPredictorDoesNotCreateProductionMeasurement ()

counterexampleMustSurviveAverageFit : CounterexampleMayBeDiscardedAfterAverageFit → ⊥
counterexampleMustSurviveAverageFit ()
