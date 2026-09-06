module DASHI.Core.ResidualSalienceSchedulerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ResidualSalienceBidiCrossPollination2026Exact as Salience
import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as Loop

------------------------------------------------------------------------
-- RECIPROCAL WELD: CONSUMER DISCRIMINATION -> NEXT PROBE
------------------------------------------------------------------------

record SalienceQualifiedMove (fibre : Loop.LiveResidualFibre) : Set₁ where
  constructor salience-qualified-move
  field
    candidate : Loop.CandidateMove fibre
    priority : Salience.ResidualSearchPriority
    residualMatchesCandidate :
      Salience.nextProbeReference priority ≡ Loop.candidateReference candidate
    rankingReference : String
open SalienceQualifiedMove public

selectQualifiedMove :
  ∀ {fibre} →
  (candidate : Loop.CandidateMove fibre) →
  (priority : Salience.ResidualSearchPriority) →
  Salience.nextProbeReference priority ≡ Loop.candidateReference candidate →
  SalienceQualifiedMove fibre
selectQualifiedMove candidate priority exact =
  salience-qualified-move candidate priority exact
    "consumer-separating residual qualifies this already-admitted move for scheduling"

data SalienceCreatesAdmission : Set where

data SmallResidualMustRankLow : Set where

salienceDoesNotCreateAdmission : SalienceCreatesAdmission → ⊥
salienceDoesNotCreateAdmission ()
smallResidualNeedNotRankLow : SmallResidualMustRankLow → ⊥
smallResidualNeedNotRankLow ()

record ResidualSalienceSchedulerBoundary : Set where
  constructor residual-salience-scheduler-boundary
  field
    salienceRanksOnlyExistingCandidates : Bool
    consumerDiscriminationMayRaisePriority : Bool
    cardinalityAloneDoesNotSetPriority : Bool

canonicalResidualSalienceSchedulerBoundary : ResidualSalienceSchedulerBoundary
canonicalResidualSalienceSchedulerBoundary =
  residual-salience-scheduler-boundary true true true
