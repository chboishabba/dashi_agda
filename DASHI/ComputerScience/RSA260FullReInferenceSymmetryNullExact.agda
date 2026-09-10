module DASHI.ComputerScience.RSA260FullReInferenceSymmetryNullExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260SymmetryStabilityNullsExact as FixedNull
import DASHI.ComputerScience.RSA260MixedActionNDimFibreInferenceExact as Mixed
import DASHI.ComputerScience.RSA260ReducerHyperfabricSourceDiligenceExact as Sources

------------------------------------------------------------------------
-- FULL RE-INFERENCE STRUCTURE-PRESERVING NULL
--
-- Every null draw preserves coarse row/column degree in the primary operator,
-- scrambles fine incidence, then reruns the structural-action pipeline from
-- scratch: joint NDim refinement, size-four class discovery, local permutation
-- family inference across retained structural fibres, operator-derived
-- requirement closure, global commutation admission, and quotient scoring.
-- The observed action family is not injected into a null draw.
------------------------------------------------------------------------

record FullReInferenceRuntimeSource : Set where
  constructor full-reinference-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    compiler : String
open FullReInferenceRuntimeSource public

currentFullReInferenceRuntimeSource : FullReInferenceRuntimeSource
currentFullReInferenceRuntimeSource = full-reinference-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_full_reinference_symmetry_null_256_oracle.c"
  "2f1200c2bf0a23024b058069fa7acd15bce2adf6"
  "90cf3c9a326cb8d2667078642fca788bbbaafa34"
  "gcc (Debian 14.2.0-19) 14.2.0"

record FullReInferenceNullReceipt : Set where
  constructor full-reinference-null-receipt
  field
    carrierCoordinates : Nat
    observedRemovedCoordinates : Nat
    observedQuotientCoordinates : Nat
    nullDraws : Nat
    degreePreservingSwitchAttemptsPerDraw : Nat
    nullMinimumRemovedCoordinates : Nat
    nullMaximumRemovedCoordinates : Nat
    nullTotalRemovedCoordinates : Nat
    nullDrawsAtLeastObserved : Nat
    empiricalPNumerator : Nat
    empiricalPDenominator : Nat
    candidateInferenceRerunInsideEachNull : Bool
    structuralFibreIntersectionRerunInsideEachNull : Bool
    requirementClosureRerunInsideEachNull : Bool
    globalCommutationRerunInsideEachNull : Bool
    quotientScoreRecomputedInsideEachNull : Bool
    observedActionFamilyInjectedIntoNull : Bool
    rowColumnDegreesPreserved : Bool
    exactGitBlobExecuted : Bool
    productionRSA260MatrixUsed : Bool
open FullReInferenceNullReceipt public

currentFullReInferenceNullReceipt : FullReInferenceNullReceipt
currentFullReInferenceNullReceipt = full-reinference-null-receipt
  256 180 76
  32 20000
  0 60 120 0
  1 33
  true true true true true
  false true true false

record FullReInferenceInterpretationBoundary : Set where
  constructor full-reinference-interpretation-boundary
  field
    observedReductionBeatsAllNullDraws : Bool
    nullMayDiscoverDifferentActionFamily : Bool
    nullMayDiscoverNonzeroReduction : Bool
    coarseDegreeStructureAloneExplainsObservedQuotient : Bool
    syntheticNullPaysProductionReduction : Bool
    lowNullPProvesUniqueMechanism : Bool
open FullReInferenceInterpretationBoundary public

canonicalFullReInferenceInterpretationBoundary : FullReInferenceInterpretationBoundary
canonicalFullReInferenceInterpretationBoundary = full-reinference-interpretation-boundary
  true true true false false false

fixedNullBoundary : FixedNull.SymmetryNullInterpretationBoundary
fixedNullBoundary = FixedNull.canonicalSymmetryNullInterpretationBoundary

mixedPolicy : Mixed.CandidateFibrePolicy
mixedPolicy = Mixed.canonicalCandidateFibrePolicy

snowballBoundary : Sources.SnowballAttributionBoundary
snowballBoundary = Sources.canonicalSnowballAttributionBoundary

------------------------------------------------------------------------
-- Next residuals.
------------------------------------------------------------------------

data FullNullResidual : Set where
  deriveEveryStructuralFibreFromNullOperator : FullNullResidual
  addConsumerConflictSelectionInsideEachNull : FullNullResidual
  runNullOnProductionMatrix : FullNullResidual
  compareProductionQuotientWorkNotOnlyCoordinates : FullNullResidual

firstFullNullResidual : FullNullResidual
firstFullNullResidual = deriveEveryStructuralFibreFromNullOperator

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data FullNullRejectionImpliesProductionSpeedup : Set where
data BetterQuotientNullPImpliesCorrectFactorisation : Set where
data SameDegreeSequenceImpliesSameFineGeometry : Set where

fullNullDoesNotCreateProductionSpeedup : FullNullRejectionImpliesProductionSpeedup → ⊥
fullNullDoesNotCreateProductionSpeedup ()

quotientNullDoesNotCreateFactorisationCorrectness : BetterQuotientNullPImpliesCorrectFactorisation → ⊥
quotientNullDoesNotCreateFactorisationCorrectness ()

sameDegreesDoNotIdentifyFineGeometry : SameDegreeSequenceImpliesSameFineGeometry → ⊥
sameDegreesDoNotIdentifyFineGeometry ()
