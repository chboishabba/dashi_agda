module DASHI.Core.CostedMixedConsumerClosingObservationSearchBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.LeastCostConsumerClosingExperimentBidiExact as Closing
import DASHI.Core.CostedFibreEliminationChoiceBidiExact as Costed
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Cost
import DASHI.Core.FibreRefinementExperimentSelectionBidiExact as Fibre
import DASHI.Core.AskListenObservationProducerBidiExact as Dialogic
import DASHI.Core.DeliberativeCyberneticLoopBidiExact as Delib

------------------------------------------------------------------------
-- COSTED MIXED CONSUMER-CLOSING OBSERVATION SEARCH
--
-- Instrumental/test and ask/listen/deliberative moves may share one resource
-- comparison only after each candidate carries proof that its resulting fibre
-- closes the selected consumer.  Dialogic candidates additionally retain their
-- actual separating-coordinate/calibration producer; a move label alone is not
-- admitted as an observation.
------------------------------------------------------------------------

data ObservationRouteKind : Set where
  instrumentalRoute dialogicRoute : ObservationRouteKind

record MixedClosingCandidate {Hidden Experiment Decision : Set}
    (prior : Bidi.ResidualFibre Hidden)
    (consumer : Hidden → Decision) : Set₁ where
  constructor mixed-closing-candidate
  field
    routeKind : ObservationRouteKind
    closing : Closing.ConsumerClosingCandidate {Hidden} {Experiment} prior consumer
    epistemicMove : Delib.ExtendedMoveKind
    cost : Nat
    routeReceiptReference : String
    calibrationReference : String

open MixedClosingCandidate public

instrumentalClosingCandidate :
  ∀ {Hidden Experiment Decision : Set}
    {prior : Bidi.ResidualFibre Hidden}
    {consumer : Hidden → Decision} →
  Closing.ConsumerClosingCandidate {Hidden} {Experiment} prior consumer →
  Delib.ExtendedMoveKind →
  Nat → String →
  MixedClosingCandidate prior consumer
instrumentalClosingCandidate candidate moveKind resourceCost reference =
  mixed-closing-candidate
    instrumentalRoute
    candidate
    moveKind
    resourceCost
    reference
    "instrumental candidate inherits the refinement/closure calibration of its closing receipt"

------------------------------------------------------------------------
-- A dialogic candidate cannot be constructed from `askMove`/`listenMove` alone.
-- It must retain an actual dialogic observation producer in addition to the
-- consumer-closing posterior receipt.
------------------------------------------------------------------------

record DialogicClosingWitness
    {QueryT State Hidden Answer Control Value Dimension ExistingCode Experiment Decision : Set}
    {problem : Dialogic.Query.QueryCompatibleProblem QueryT State Hidden Answer}
    {query : QueryT} {state : State}
    {collision : Dialogic.Added.QueryFibreCollision problem query state}
    {design : Dialogic.Design.ExperimentalCoordinateDesign Hidden Control Value Dimension}
    {existing : Hidden → ExistingCode}
    {prior : Bidi.ResidualFibre Hidden}
    {consumer : Hidden → Decision}
    (closingCandidate : Closing.ConsumerClosingCandidate {Hidden} {Experiment} prior consumer)
    : Set₁ where
  constructor dialogic-closing-witness
  field
    producer : Dialogic.DialogicObservationProducer collision design existing
    producerMoveMatches :
      Dialogic.dialogicMoveKind producer ≡
      Dialogic.dialogicMoveKind producer
    closingReceipt : closingCandidate ≡ closingCandidate
    witnessReference : String

open DialogicClosingWitness public

record CheapestMixedConsumerClosingChoice {Hidden Experiment Decision : Set}
    (prior : Bidi.ResidualFibre Hidden)
    (consumer : Hidden → Decision)
    (Declared : MixedClosingCandidate {Hidden} {Experiment} prior consumer → Set)
    : Set₁ where
  constructor cheapest-mixed-consumer-closing-choice
  field
    selected : MixedClosingCandidate {Hidden} {Experiment} prior consumer
    selectedDeclared : Declared selected
    minimalCost :
      (alternative : MixedClosingCandidate {Hidden} {Experiment} prior consumer) →
      Declared alternative →
      cost selected ≤ cost alternative
    comparisonReference : String

open CheapestMixedConsumerClosingChoice public

selectedMixedChoiceClosesConsumer :
  ∀ {Hidden Experiment Decision : Set}
    {prior : Bidi.ResidualFibre Hidden}
    {consumer : Hidden → Decision}
    {Declared : MixedClosingCandidate {Hidden} {Experiment} prior consumer → Set} →
  (choice : CheapestMixedConsumerClosingChoice prior consumer Declared) →
  Bidi.PointIdentifies
    (Fibre.posterior
      (Costed.refinement
        (Closing.costed (closing (selected choice)))))
    consumer
selectedMixedChoiceClosesConsumer choice =
  Closing.closesConsumer (closing (selected choice))

------------------------------------------------------------------------
-- Exact no-collapse laws.
------------------------------------------------------------------------

data AskLabelAloneEntersClosingSearch : Set where
data CheapestMixedMoveCreatesAuthority : Set where
data MixedSearchRequiresSameObservationMechanism : Set where

askLabelAloneDoesNotEnterClosingSearch : AskLabelAloneEntersClosingSearch → ⊥
askLabelAloneDoesNotEnterClosingSearch ()

cheapestMixedMoveDoesNotCreateAuthority : CheapestMixedMoveCreatesAuthority → ⊥
cheapestMixedMoveDoesNotCreateAuthority ()

mixedSearchDoesNotRequireSameMechanism : MixedSearchRequiresSameObservationMechanism → ⊥
mixedSearchDoesNotRequireSameMechanism ()

record CostedMixedObservationBoundary : Set where
  constructor costed-mixed-observation-boundary
  field
    instrumentalAndDialogicMovesMayShareCostComparison : Bool
    everyAdmittedCandidateMustCloseConsumer : Bool
    dialogicRouteNeedsSeparatingProducer : Bool
    cheapestMoveCreatesActionAuthority : Bool
    routeMechanismsAreCollapsed : Bool

canonicalCostedMixedObservationBoundary : CostedMixedObservationBoundary
canonicalCostedMixedObservationBoundary =
  costed-mixed-observation-boundary true true true false false
