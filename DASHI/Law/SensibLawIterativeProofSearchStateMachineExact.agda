module DASHI.Law.SensibLawIterativeProofSearchStateMachineExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofGapExecutableSearchCompilerExact as Compiler
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Result
import DASHI.Law.SensibLawProofSearchParetoSaturationExact as Pareto

------------------------------------------------------------------------
-- ITERATIVE CONSUMER-RELATIVE SEARCH STATE MACHINE
------------------------------------------------------------------------

data ProofSearchTerminalState : Set where
  proofClosed
  proofContested
  proofAuthorityBlocked
  proofUnderidentified
  proofSaturated
  : ProofSearchTerminalState

data ProofSearchProgressState : Set where
  searchNeedsPlan
  searchPlanReady
  searchAcquired
  searchAssessed
  searchFrontierUpdated
  : ProofSearchProgressState

record ProofSearchFrontier : Set where
  constructor proofSearchFrontier
  field
    consumerReference : String
    frontierReference : String
    firstResidualReference : String
    openGapCount : Nat
    contestedGapCount : Nat
    frontierReferenceReceipt : Set

open ProofSearchFrontier public

record ProofSearchIteration : Set₁ where
  constructor proofSearchIteration
  field
    iterationIndex : Nat
    priorFrontier : ProofSearchFrontier
    plan : Compiler.ProofGapSearchPlan
    planTargetsPriorFrontierReceipt : Set
    returnCompilation : Compiler.SearchReturnCompilation
    resultDelta : Result.SearchFrontierDelta
    returnDeltaMatchesReceipt : Set
    posteriorFrontier : ProofSearchFrontier
    posteriorMatchesDeltaReceipt : Set
    iterationReference : String

open ProofSearchIteration public

record IterativeProofSearchTrace : Set₁ where
  constructor iterativeProofSearchTrace
  field
    initialFrontier : ProofSearchFrontier
    iterations : List ProofSearchIteration
    currentFrontier : ProofSearchFrontier
    currentFrontierReachableFromTraceReceipt : Set
    traceReference : String

open IterativeProofSearchTrace public

record ProofSearchContinuation : Set where
  constructor proofSearchContinuation
  field
    frontierReference : String
    decision : Pareto.SearchContinuationDecision
    decisionReference : String

open ProofSearchContinuation public

record ProofSearchTermination : Set₁ where
  constructor proofSearchTermination
  field
    trace : IterativeProofSearchTrace
    terminalState : ProofSearchTerminalState
    terminalReceipt : Set
    saturationReceiptReference : String
    exactRemainingResidualReference : String
    terminationReference : String

open ProofSearchTermination public

------------------------------------------------------------------------
-- Canonical interpretation of frontier deltas.
------------------------------------------------------------------------

terminalForDelta : Result.FrontierChange → Bool
terminalForDelta Result.frontierClosed = true
terminalForDelta Result.frontierContradicted = true
terminalForDelta Result.frontierUnderidentified = true
terminalForDelta Result.frontierUnchanged = false
terminalForDelta Result.frontierNarrowed = false
terminalForDelta Result.frontierReopened = false

closedDeltaIsTerminal : terminalForDelta Result.frontierClosed ≡ true
closedDeltaIsTerminal = refl

narrowedDeltaContinues : terminalForDelta Result.frontierNarrowed ≡ false
narrowedDeltaContinues = refl

------------------------------------------------------------------------
-- Search does not terminate merely because one query failed to change the
-- frontier; saturation remains the stronger multi-family receipt.
------------------------------------------------------------------------

data OneUnchangedDeltaMeansSaturated : Set where
data OneRejectedResultMeansAuthorityBlocked : Set where
data OneContradictionMeansUniqueFinalDoctrine : Set where
data IterationCountAloneDefinesCompletion : Set where

data SearchMayContinueAfterClosure : Set where

oneUnchangedDeltaDoesNotSaturate : OneUnchangedDeltaMeansSaturated → ⊥
oneUnchangedDeltaDoesNotSaturate ()

oneRejectedResultDoesNotAuthorityBlock : OneRejectedResultMeansAuthorityBlocked → ⊥
oneRejectedResultDoesNotAuthorityBlock ()

contradictionDoesNotUniquelyResolveDoctrine : OneContradictionMeansUniqueFinalDoctrine → ⊥
contradictionDoesNotUniquelyResolveDoctrine ()

iterationCountDoesNotDefineCompletion : IterationCountAloneDefinesCompletion → ⊥
iterationCountDoesNotDefineCompletion ()

closedConsumerDoesNotKeepSearching : SearchMayContinueAfterClosure → ⊥
closedConsumerDoesNotKeepSearching ()

record IterativeProofSearchBoundary : Set where
  constructor iterativeProofSearchBoundary
  field
    searchIsConsumerRelative : Bool
    searchIsConsumerRelativeIsTrue : searchIsConsumerRelative ≡ true
    eachRoundReturnsFrontierDelta : Bool
    eachRoundReturnsFrontierDeltaIsTrue : eachRoundReturnsFrontierDelta ≡ true
    unchangedSingleRoundEqualsSaturation : Bool
    unchangedSingleRoundEqualsSaturationIsFalse : unchangedSingleRoundEqualsSaturation ≡ false
    terminalStatesExposeResidualOrClosure : Bool
    terminalStatesExposeResidualOrClosureIsTrue : terminalStatesExposeResidualOrClosure ≡ true
    closedConsumerContinuesAcquisition : Bool
    closedConsumerContinuesAcquisitionIsFalse : closedConsumerContinuesAcquisition ≡ false

canonicalIterativeProofSearchBoundary : IterativeProofSearchBoundary
canonicalIterativeProofSearchBoundary =
  iterativeProofSearchBoundary true refl true refl false refl true refl false refl
