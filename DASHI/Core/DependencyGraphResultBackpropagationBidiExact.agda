module DASHI.Core.DependencyGraphResultBackpropagationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedProvenanceDependencyGraphExact as Graph
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Backprop

------------------------------------------------------------------------
-- RESULT BACKPROPAGATION AS REVERSE DEPENDENCY TRAVERSAL
--
-- Forward dependency edges say what a source contributed to a target.
-- Backpropagation runs in the reverse direction: when a result diagnoses a
-- coordinate, only required edges whose role owns that coordinate qualify as
-- immediate reopen edges.  Their sources become an inspection frontier; they
-- are not automatically declared false.
------------------------------------------------------------------------

record ReverseReopenEdge
    (edge : Graph.DependencyEdge)
    (coordinate : Backprop.ReopenCoordinate) : Set where
  constructor reverse-reopen-edge
  field
    required : Graph.requiredForTarget edge ≡ true
    coordinateMatchesRole :
      coordinate ≡ Backprop.reopenForRole (Graph.role edge)
    backpropReference : String

open ReverseReopenEdge public

record ResultBackpropEdge
    (assessmentOutcome : Backprop.ExperimentalOutcome)
    (assessmentDiagnosis : Backprop.OutcomeDiagnosis)
    (edge : Graph.DependencyEdge) : Set where
  constructor result-backprop-edge
  field
    reverseEdge :
      ReverseReopenEdge edge
        (Backprop.reopenFor assessmentOutcome assessmentDiagnosis)
    resultReference : String

open ResultBackpropEdge public

backpropSource :
  ∀ {outcome diagnosis edge} →
  ResultBackpropEdge outcome diagnosis edge →
  Graph.DependencyNode
backpropSource {edge = edge} receipt = Graph.sourceNode edge

backpropTarget :
  ∀ {outcome diagnosis edge} →
  ResultBackpropEdge outcome diagnosis edge →
  Graph.DependencyNode
backpropTarget {edge = edge} receipt = Graph.targetNode edge

------------------------------------------------------------------------
-- Exact finite dependency graph.
------------------------------------------------------------------------

observationNode : Graph.DependencyNode
observationNode = Graph.dependencyNode
  "experiment observation"
  Graph.runtimeAcquisition
  "observed coordinate used by model/consumer"
  false

frameNode : Graph.DependencyNode
frameNode = Graph.dependencyNode
  "interpretive frame"
  Graph.dashiFormal
  "representation/orientation frame"
  false

modelNode : Graph.DependencyNode
modelNode = Graph.dependencyNode
  "working model"
  Graph.dashiFormal
  "model used to compile a consumer answer"
  false

consumerNode : Graph.DependencyNode
consumerNode = Graph.dependencyNode
  "declared consumer closure"
  Graph.dashiFormal
  "consumer-relative terminal answer"
  false

observationToConsumer : Graph.DependencyEdge
observationToConsumer = Graph.dependencyEdge
  observationNode consumerNode Graph.evidenceRole true
  "measurement-derived closure depends directly on the admitted observation"

frameToConsumer : Graph.DependencyEdge
frameToConsumer = Graph.dependencyEdge
  frameNode consumerNode Graph.projectionRole true
  "orientation/representation frame is required for this interpreted closure"

modelToConsumer : Graph.DependencyEdge
modelToConsumer = Graph.dependencyEdge
  modelNode consumerNode Graph.definitionRole true
  "working model is required for this compiled consumer answer"

observationToModel : Graph.DependencyEdge
observationToModel = Graph.dependencyEdge
  observationNode modelNode Graph.evidenceRole true
  "model fit/selection depends on the acquired observation"

canonicalBackpropGraph : Graph.TypedDependencyGraph
canonicalBackpropGraph = Graph.typedDependencyGraph
  "result-sensitive closure dependency graph"
  (observationNode ∷ frameNode ∷ modelNode ∷ consumerNode ∷ [])
  (observationToConsumer ∷ frameToConsumer ∷ modelToConsumer ∷ observationToModel ∷ [])

------------------------------------------------------------------------
-- Exact reverse edges for different result diagnoses.
------------------------------------------------------------------------

adverseModelBackpropEdge :
  ResultBackpropEdge Backprop.adverse Backprop.modelConflict modelToConsumer
adverseModelBackpropEdge =
  result-backprop-edge
    (reverse-reopen-edge refl refl
      "reverse the required model->consumer dependency; reopen model inspection")
    "adverse result diagnosed as model conflict"

indeterminateObservationBackpropEdge :
  ResultBackpropEdge
    Backprop.indeterminate Backprop.insufficientResolution observationToConsumer
indeterminateObservationBackpropEdge =
  result-backprop-edge
    (reverse-reopen-edge refl refl
      "reverse the required observation->consumer dependency; reacquire/resolve observation")
    "indeterminate result diagnosed as insufficient resolution"

adverseFrameBackpropEdge :
  ResultBackpropEdge Backprop.adverse Backprop.frameConflict frameToConsumer
adverseFrameBackpropEdge =
  result-backprop-edge
    (reverse-reopen-edge refl refl
      "reverse the required frame->consumer dependency; rechart before changing conclusion")
    "adverse result diagnosed as orientation/frame conflict"

adverseModelBackpropReachesModel :
  backpropSource adverseModelBackpropEdge ≡ modelNode
adverseModelBackpropReachesModel = refl

indeterminateBackpropReachesObservation :
  backpropSource indeterminateObservationBackpropEdge ≡ observationNode
indeterminateBackpropReachesObservation = refl

frameConflictBackpropReachesFrame :
  backpropSource adverseFrameBackpropEdge ≡ frameNode
frameConflictBackpropReachesFrame = refl

------------------------------------------------------------------------
-- The reopened source exposes its own upstream dependency frontier, but reverse
-- traversal does not automatically mark every ancestor false.
------------------------------------------------------------------------

record UpstreamInspectionFrontier : Set where
  constructor upstream-inspection-frontier
  field
    reopenedNode : Graph.DependencyNode
    upstreamEdge : Graph.DependencyEdge
    upstreamTargetsReopenedNode :
      Graph.targetNode upstreamEdge ≡ reopenedNode
    inspectionReference : String

open UpstreamInspectionFrontier public

modelConflictExposesObservationDependency : UpstreamInspectionFrontier
modelConflictExposesObservationDependency =
  upstream-inspection-frontier modelNode observationToModel refl
    "after reopening the model, inspect the observation dependency without declaring it false"

data ReverseTraversalRefutesEveryAncestor : Set where
data NegativeResultTraversesEveryIncomingEdge : Set where
data ReopenedSourceIsAutomaticallyFalse : Set where

reverseTraversalDoesNotRefuteEveryAncestor :
  ReverseTraversalRefutesEveryAncestor → ⊥
reverseTraversalDoesNotRefuteEveryAncestor ()

negativeResultDoesNotTraverseEveryIncomingEdge :
  NegativeResultTraversesEveryIncomingEdge → ⊥
negativeResultDoesNotTraverseEveryIncomingEdge ()

reopenedSourceIsNotAutomaticallyFalse : ReopenedSourceIsAutomaticallyFalse → ⊥
reopenedSourceIsNotAutomaticallyFalse ()

record DependencyGraphBackpropagationBoundary : Set where
  constructor dependency-graph-backpropagation-boundary
  field
    backpropRunsAgainstForwardDependencyDirection : Bool
    requiredRoleMustMatchDiagnosedCoordinate : Bool
    reopenedSourceBecomesInspectionFrontier : Bool
    reopenedSourceAutomaticallyFalse : Bool
    adverseResultTraversesAllDependencies : Bool
    graphBackpropErasesProvenance : Bool

canonicalDependencyGraphBackpropagationBoundary :
  DependencyGraphBackpropagationBoundary
canonicalDependencyGraphBackpropagationBoundary =
  dependency-graph-backpropagation-boundary true true true false false false
