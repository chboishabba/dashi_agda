module DASHI.Environment.AssimilationDependencyReopeningExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Assimilation changes scientific state; dependency closure determines which
-- derived artifacts must reopen.  This module gives a concrete exact LES chain
-- and, importantly, proves an unrelated artifact is outside that closure.
------------------------------------------------------------------------

open import Data.Empty using (⊥)

import DASHI.Core.AffectedDependencyClosureExact as Closure


data Artifact : Set where
  newObservation stateEstimate modelRun candidatePlan unrelatedArchive : Artifact

data Depends : Artifact → Artifact → Set where
  observationUpdatesState : Depends newObservation stateEstimate
  stateChangesModelRun : Depends stateEstimate modelRun
  modelRunChangesPlan : Depends modelRun candidatePlan

observationReopensState :
  Closure.ReopeningObligation Depends newObservation stateEstimate
observationReopensState =
  Closure.oneEdgeCreatesReopeningObligation observationUpdatesState

stateReopensModel :
  Closure.ReopeningObligation Depends stateEstimate modelRun
stateReopensModel =
  Closure.oneEdgeCreatesReopeningObligation stateChangesModelRun

modelReopensPlan :
  Closure.ReopeningObligation Depends modelRun candidatePlan
modelReopensPlan =
  Closure.oneEdgeCreatesReopeningObligation modelRunChangesPlan

observationReopensPlan :
  Closure.ReopeningObligation Depends newObservation candidatePlan
observationReopensPlan =
  Closure.obligationsCompose observationReopensState
    (Closure.obligationsCompose stateReopensModel modelReopensPlan)

noPlanToUnrelated :
  Closure.AffectedClosure Depends candidatePlan unrelatedArchive → ⊥
noPlanToUnrelated ()

noModelToUnrelated :
  Closure.AffectedClosure Depends modelRun unrelatedArchive → ⊥
noModelToUnrelated (Closure.affectedStep modelRunChangesPlan rest) =
  noPlanToUnrelated rest

noStateToUnrelated :
  Closure.AffectedClosure Depends stateEstimate unrelatedArchive → ⊥
noStateToUnrelated (Closure.affectedStep stateChangesModelRun rest) =
  noModelToUnrelated rest

observationDoesNotForceUnrelatedArchiveReopen :
  Closure.AffectedClosure Depends newObservation unrelatedArchive → ⊥
observationDoesNotForceUnrelatedArchiveReopen
  (Closure.affectedStep observationUpdatesState rest) =
  noStateToUnrelated rest
