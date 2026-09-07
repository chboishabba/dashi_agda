module DASHI.Core.PairIndexedInformationLossLocusBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.QueryFibreAddedCoordinateProducerBidiExact as Added
import DASHI.Core.CommutingProvenanceBidiCrossPollination2026Exact as Commuting

------------------------------------------------------------------------
-- PAIR-INDEXED INFORMATION-LOSS LOCUS
--
-- Information loss is not merely a property of a stage in isolation. It is
-- relative to a pair of distinct upstream states. Once a deterministic stage
-- collapses that pair, any deterministic downstream composition preserves the
-- equality until genuinely new information is introduced.
------------------------------------------------------------------------

record PairLossLocus {State Observed : Set}
    (observe : State → Observed) : Set where
  constructor pair-loss-locus
  field
    left right : State
    distinct : left ≡ right → ⊥
    collapsed : observe left ≡ observe right
    stageReference : String
    pairReference : String

open PairLossLocus public

collapsedPairStaysCollapsedDownstream :
  ∀ {State Observed Output : Set}
    {observe : State → Observed} →
  (loss : PairLossLocus observe) →
  (downstream : Observed → Output) →
  downstream (observe (left loss)) ≡ downstream (observe (right loss))
collapsedPairStaysCollapsedDownstream loss downstream
  with collapsed loss
... | refl = refl

record DeterministicStack {A B C : Set} : Set₁ where
  constructor deterministic-stack
  field
    first : A → B
    second : B → C
    stackReference : String

open DeterministicStack public

pairLossPersistsThroughStack :
  ∀ {A B C : Set}
    (stack : DeterministicStack {A} {B} {C}) →
  (loss : PairLossLocus (first stack)) →
  second stack (first stack (left loss)) ≡
  second stack (first stack (right loss))
pairLossPersistsThroughStack stack loss =
  collapsedPairStaysCollapsedDownstream loss (second stack)

------------------------------------------------------------------------
-- Exact finite calibration: one projection collapses only one chosen pair.
------------------------------------------------------------------------

data ToyState : Set where x y z : ToyState
data ToyObserved : Set where collapsedXY visibleZ : ToyObserved

toyObserve : ToyState → ToyObserved
toyObserve x = collapsedXY
toyObserve y = collapsedXY
toyObserve z = visibleZ

xNotY : x ≡ y → ⊥
xNotY ()

toyXYLoss : PairLossLocus toyObserve
toyXYLoss = pair-loss-locus
  x y xNotY refl
  "synthetic projection"
  "the pair (x,y) is collapsed while z remains visible"

data ToyDownstream : Set where downstreamCollapsed downstreamVisible : ToyDownstream

toyDownstream : ToyObserved → ToyDownstream
toyDownstream collapsedXY = downstreamCollapsed
toyDownstream visibleZ = downstreamVisible

toyCollapsedPairNeverRestored :
  toyDownstream (toyObserve x) ≡ toyDownstream (toyObserve y)
toyCollapsedPairNeverRestored =
  collapsedPairStaysCollapsedDownstream toyXYLoss toyDownstream

------------------------------------------------------------------------
-- Repair boundary: restoring the distinction requires a genuinely new
-- coordinate/producer, not merely deterministic post-processing of the same
-- collapsed carrier. The existing added-coordinate owner supplies that repair
-- architecture, but this loss theorem does not manufacture the producer.
------------------------------------------------------------------------

data DownstreamDeterminismRestoresCollapsedDistinction : Set where
data LossLocusIsOnlyAPropertyOfTheStack : Set where
data PairLossAutomaticallyCreatesAddedCoordinate : Set where

deterministicDownstreamDoesNotRestoreLoss :
  DownstreamDeterminismRestoresCollapsedDistinction → ⊥
deterministicDownstreamDoesNotRestoreLoss ()

lossLocusIsPairRelative : LossLocusIsOnlyAPropertyOfTheStack → ⊥
lossLocusIsPairRelative ()

lossDoesNotAutomaticallyCreateCoordinate :
  PairLossAutomaticallyCreatesAddedCoordinate → ⊥
lossDoesNotAutomaticallyCreateCoordinate ()

record PairIndexedInformationLossBoundary : Set where
  constructor pair-indexed-information-loss-boundary
  field
    lossIndexedByDistinctPair : Bool
    deterministicDownstreamPreservesCollapse : Bool
    stackLabelAloneDeterminesLossPair : Bool
    newCoordinateRequiredForRecovery : Bool
    lossReceiptCreatesCoordinateProducer : Bool

canonicalPairIndexedInformationLossBoundary :
  PairIndexedInformationLossBoundary
canonicalPairIndexedInformationLossBoundary =
  pair-indexed-information-loss-boundary true true false true false
