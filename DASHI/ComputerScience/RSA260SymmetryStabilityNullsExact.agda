module DASHI.ComputerScience.RSA260SymmetryStabilityNullsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260MixedActionNDimFibreInferenceExact as Mixed
import DASHI.ComputerScience.RSA260ReducerHyperfabricSourceDiligenceExact as Sources

------------------------------------------------------------------------
-- FLY-STYLE STRUCTURE-PRESERVING SYMMETRY NULL
--
-- Preserve coarse row/column degree exactly, scramble fine incidence by
-- degree-preserving 2x2 switches, and recompute the observed V4 component
-- symmetry score.  This is a synthetic mechanism test only.
------------------------------------------------------------------------

record SymmetryNullRuntimeSource : Set where
  constructor symmetry-null-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    compiler : String
open SymmetryNullRuntimeSource public

currentSymmetryNullRuntimeSource : SymmetryNullRuntimeSource
currentSymmetryNullRuntimeSource = symmetry-null-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_symmetry_stability_nulls_256_oracle.c"
  "4443700a5e8e5f9d16458ff207c1f0cb2da7d85f"
  "fccad5f85f4e2adea4e913d5e9246d58be5b6211"
  "gcc (Debian 14.2.0-19) 14.2.0"

record SymmetryNullExecutionReceipt : Set where
  constructor symmetry-null-execution-receipt
  field
    carrierCoordinates : Nat
    observedV4SymmetryComponents : Nat
    nullDraws : Nat
    degreePreservingSwitchesPerDraw : Nat
    nullMinimumSymmetryScore : Nat
    nullMaximumSymmetryScore : Nat
    nullTotalSymmetryScore : Nat
    nullDrawsAtLeastObserved : Nat
    nullDrawsEqualObserved : Nat
    empiricalPNumerator : Nat
    empiricalPDenominator : Nat
    rowDegreesPreservedExactly : Bool
    columnDegreesPreservedExactly : Bool
    fineIncidenceScrambled : Bool
    sourceEquivalentExecutionPassed : Bool
    exactGitBlobExecuted : Bool
    productionRSA260MatrixUsed : Bool
open SymmetryNullExecutionReceipt public

currentSymmetryNullExecutionReceipt : SymmetryNullExecutionReceipt
currentSymmetryNullExecutionReceipt = symmetry-null-execution-receipt
  256 3 64 20000 0 0 0 0 0 1 65
  true true true true true false

record SymmetryNullInterpretationBoundary : Set where
  constructor symmetry-null-interpretation-boundary
  field
    coarseDegreeStructureInsufficientForObservedSymmetry : Bool
    finePairwiseGeometryMattersOnSyntheticBenchmark : Bool
    empiricalNullRejectsAtFivePercentOnSyntheticBenchmark : Bool
    syntheticNullImpliesProductionSpeedup : Bool
    nullPValueCreatesMechanismProof : Bool
    preservedDegreesImplySameMatrix : Bool
open SymmetryNullInterpretationBoundary public

canonicalSymmetryNullInterpretationBoundary : SymmetryNullInterpretationBoundary
canonicalSymmetryNullInterpretationBoundary = symmetry-null-interpretation-boundary
  true true true false false false

mixedCandidateFibrePolicy : Mixed.CandidateFibrePolicy
mixedCandidateFibrePolicy = Mixed.canonicalCandidateFibrePolicy

snowballBoundary : Sources.SnowballAttributionBoundary
snowballBoundary = Sources.canonicalSnowballAttributionBoundary

------------------------------------------------------------------------
-- Next residual: rerun full inferred-action hyperfabric inside every null draw,
-- rather than scoring only the already identified V4 component family.
------------------------------------------------------------------------

data SymmetryNullResidual : Set where
  rerunCandidateInferenceInsideEachNull : SymmetryNullResidual
  rerunRequirementClosureInsideEachNull : SymmetryNullResidual
  rerunConflictSelectionInsideEachNull : SymmetryNullResidual
  compareQuotientFactorDistribution : SymmetryNullResidual
  runProductionStructurePreservingNull : SymmetryNullResidual

firstSymmetryNullResidual : SymmetryNullResidual
firstSymmetryNullResidual = rerunCandidateInferenceInsideEachNull

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data LowNullPImpliesProductionMechanism : Set where
data SameDegreeSequenceImpliesSameOperator : Set where
data NullRejectionImpliesCausalMechanism : Set where

lowNullPDoesNotCreateProductionMechanism : LowNullPImpliesProductionMechanism → ⊥
lowNullPDoesNotCreateProductionMechanism ()

sameDegreeSequenceDoesNotIdentifyOperator : SameDegreeSequenceImpliesSameOperator → ⊥
sameDegreeSequenceDoesNotIdentifyOperator ()

nullRejectionDoesNotCreateCausality : NullRejectionImpliesCausalMechanism → ⊥
nullRejectionDoesNotCreateCausality ()
