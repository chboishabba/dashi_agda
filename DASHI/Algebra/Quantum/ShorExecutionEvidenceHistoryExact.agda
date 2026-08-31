module DASHI.Algebra.Quantum.ShorExecutionEvidenceHistoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.TrajectoryResidueExact as Residue
import DASHI.Algebra.Quantum.GeneralShor as Shor

------------------------------------------------------------------------
-- SHOR EXECUTION EVIDENCE AS PROOF-RELEVANT HISTORY
--
-- GeneralShor already keeps successful-sample evidence separate from
-- probability evidence.  This owner adds only the temporal/provenance seam:
-- a successful recovery remains attached to the exact executed seed/sample
-- occurrence that justified it.
------------------------------------------------------------------------

record Attempt
    {H : Shor.HiddenPeriodProblem}
    (machine : Shor.ShorPeriodFindingMachine H) : Set where
  constructor attempt
  field
    seed : Nat
    sample : Shor.PeriodSample machine
    sampleIsExecution : sample ≡ Shor.periodExecute machine seed
    attemptReference : String

open Attempt public

AttemptHistory :
  ∀ {H : Shor.HiddenPeriodProblem} →
  Shor.ShorPeriodFindingMachine H → Set
AttemptHistory machine = List (Attempt machine)

data AttemptOccurs
    {H : Shor.HiddenPeriodProblem}
    {machine : Shor.ShorPeriodFindingMachine H}
    (entry : Attempt machine) : AttemptHistory machine → Set where
  occursHere : ∀ {rest} → AttemptOccurs entry (entry ∷ rest)
  occursLater :
    ∀ {other rest} →
    AttemptOccurs entry rest →
    AttemptOccurs entry (other ∷ rest)

historyResidue :
  ∀ {H : Shor.HiddenPeriodProblem}
    {machine : Shor.ShorPeriodFindingMachine H} →
  AttemptHistory machine → Residue.ResidueFlag
historyResidue [] = Residue.residueAbsent
historyResidue (_ ∷ _) = Residue.residuePresent

data HistoryStep
    {H : Shor.HiddenPeriodProblem}
    (machine : Shor.ShorPeriodFindingMachine H) :
    AttemptHistory machine → AttemptHistory machine → Set where
  recordAttempt :
    ∀ {history} (entry : Attempt machine) →
    HistoryStep machine history (entry ∷ history)

attemptHistoryNoErasure :
  ∀ {H : Shor.HiddenPeriodProblem}
    {machine : Shor.ShorPeriodFindingMachine H} →
  Residue.NoResidueErasure
    (HistoryStep machine)
    historyResidue
attemptHistoryNoErasure (recordAttempt entry) present = refl

------------------------------------------------------------------------
-- Exact successful attempt receipt.
------------------------------------------------------------------------

record HistoricalShorSuccess
    {H : Shor.HiddenPeriodProblem}
    (machine : Shor.ShorPeriodFindingMachine H) : Set₁ where
  constructor historicalShorSuccess
  field
    evidence : Shor.ShorSuccessEvidence machine
    execution : Attempt machine
    executionSeedMatches : seed execution ≡ Shor.seed evidence
    executionSampleMatches :
      sample execution ≡ Shor.periodExecute machine (Shor.seed evidence)
    history : AttemptHistory machine
    executionOccurs : AttemptOccurs execution history
    successReference : String

open HistoricalShorSuccess public

historicalRecoveredPeriodIsExact :
  ∀ {H : Shor.HiddenPeriodProblem}
    {machine : Shor.ShorPeriodFindingMachine H} →
  HistoricalShorSuccess machine →
  Shor.recoverPeriod machine
    (Shor.periodExecute machine
      (Shor.seed (evidence _)))
  ≡ Shor.period H
historicalRecoveredPeriodIsExact success =
  Shor.recoveredPeriodIsExact _ (evidence success)

------------------------------------------------------------------------
-- Evidence separation remains unchanged by adding history.
------------------------------------------------------------------------

record ShorExecutionHistoryBoundary : Set where
  constructor shorExecutionHistoryBoundary
  field
    successfulSampleRetainsExactHistory : Bool
    successfulSampleRetainsExactHistoryIsTrue :
      successfulSampleRetainsExactHistory ≡ true
    oneSuccessfulExecutionProvesProbabilityLowerBound : Bool
    oneSuccessfulExecutionProvesProbabilityLowerBoundIsFalse :
      oneSuccessfulExecutionProvesProbabilityLowerBound ≡ false
    executionHistoryProvesQuantumSpeedup : Bool
    executionHistoryProvesQuantumSpeedupIsFalse :
      executionHistoryProvesQuantumSpeedup ≡ false
    executionHistoryProvesPhysicalDeviceImplementation : Bool
    executionHistoryProvesPhysicalDeviceImplementationIsFalse :
      executionHistoryProvesPhysicalDeviceImplementation ≡ false

canonicalShorExecutionHistoryBoundary : ShorExecutionHistoryBoundary
canonicalShorExecutionHistoryBoundary =
  shorExecutionHistoryBoundary
    true refl
    false refl
    false refl
    false refl
