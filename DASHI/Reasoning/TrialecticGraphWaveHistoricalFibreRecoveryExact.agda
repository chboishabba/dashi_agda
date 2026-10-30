{-# OPTIONS --safe #-}
module DASHI.Reasoning.TrialecticGraphWaveHistoricalFibreRecoveryExact where

------------------------------------------------------------------------
-- HISTORY-RETAINING GRAPH -> WAVE CONSUMER RECOVERY, 2026-10-30.
--
-- Reuse-first owners:
--  TrialecticObserverMatrix369Exact: literal nine directed positions.
--  TrialecticDirectedSourceTargetHyperfabricExact: outgoing/incoming
--    source/target incidence (two oriented roles per directed edge).
--  Trialectic369RubikRefinementExact: trit-typed 3x3 -> rank-three
--    depth-3 ternary address (27 choices per refinement stage).
--  Trialectic369OutgoingFrickeModeBlock18Exact: DIFFERENT 2x9 phase
--    carrier; no false identity with 18 directed incidence roles.
--  Core.ConsumerIndexedResidualRefinementExact, Blackwell (1953)
--    and Cousot-Cousot (1977) method precedents.
--  Reasoning.HistoryTimeIndexedConsumerFibreExact:
--    history/time-indexed producer and consumer versions.
--  Reasoning.HistoryTimeReasoningFibreTransportPathExact:
--    path retains intermediate states and attachments.
--  Core.ConsumerIndexedUntanglingTowerExact: nested exact reopening.
--  Physics.WaveAlgorithmLift: a wave refinement tower needs explicit
--    projection/evolution/observation commutation.
--
-- This module corrects the STATIC C3 non-descent story: a history
-- that retains the original directed matrix DOES recover the signed
-- consumer, including after an explicitly compatible dynamics step.
-- The negative criterion is collision of COMPLETE retained histories,
-- not coincidence of a single orbit-summed 3x3 matrix.
--
-- All results below are generic finite relational results, not
-- prime distribution, analytic pi phase, Monster 3B or a proof of
-- wave interference. Attribution remains independent.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import DASHI.Reasoning.TrialecticWeightedDirectedGraph369Exact as Graph
import DASHI.Reasoning.TrialecticC3WeightedOrbitSymmetrizationExact as Orbit
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Matrix
import DASHI.Reasoning.TrialecticGraphWaveConsumerLossCutExact as Static
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Reasoning.HistoryTimeIndexedConsumerFibreExact as History
import DASHI.Reasoning.HistoryTimeReasoningFibreTransportPathExact as Path
import DASHI.Core.ConsumerIndexedUntanglingTowerExact as Tower
import DASHI.Physics.WaveAlgorithmLift as Wave
import DASHI.Reasoning.TrialecticDirectedSourceTargetHyperfabricExact as Directed
import DASHI.Reasoning.Trialectic369RubikRefinementExact as Cube
import DASHI.Reasoning.Trialectic369OutgoingFrickeModeBlock18Exact as Mode18
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper

-- A path point records its own original fine matrix; an orbit-sum is
-- only a derived observation. This is ONE concrete source-history
-- carrier, not an assumption that all physical histories are lossless.
record RetainedGraphHistory : Set where
  constructor retained-graph-history
  field
    before : Graph.WeightedMatrix3
    current : Graph.WeightedMatrix3
    after : Graph.WeightedMatrix3
open RetainedGraphHistory public

graphAtBefore : RetainedGraphHistory -> Graph.WeightedDigraph3
graphAtBefore h = Graph.matrixToDigraph (before h)

graphAtCurrent : RetainedGraphHistory -> Graph.WeightedDigraph3
graphAtCurrent h = Graph.matrixToDigraph (current h)

graphAtAfter : RetainedGraphHistory -> Graph.WeightedDigraph3
graphAtAfter h = Graph.matrixToDigraph (after h)

-- Coarse published history: the three original C3-averaged frames.
record CoarseGraphHistory : Set where
  constructor coarse-graph-history
  field
    beforeOrbit currentOrbit afterOrbit : Graph.WeightedMatrix3
open CoarseGraphHistory public

coarseHistory : RetainedGraphHistory -> CoarseGraphHistory
coarseHistory h = coarse-graph-history
  (Static.orbitMatrix (graphAtBefore h))
  (Static.orbitMatrix (graphAtCurrent h))
  (Static.orbitMatrix (graphAtAfter h))

-- Fine history includes ALL three matrices. This makes source and
-- target edge weights recoverable even when the C3 averages collide.
retainedObserver : RetainedGraphHistory ->
  CoarseGraphHistory × RetainedGraphHistory
retainedObserver h = coarseHistory h , h

data HistoryTime : Set where
  priorTime : HistoryTime
  liveTime : HistoryTime
  futureTime : HistoryTime

fineGraphAt : HistoryTime -> RetainedGraphHistory ->
  Graph.WeightedDigraph3
fineGraphAt priorTime = graphAtBefore
fineGraphAt liveTime = graphAtCurrent
fineGraphAt futureTime = graphAtAfter

selectedConsumerAt : HistoryTime -> RetainedGraphHistory -> Nat
selectedConsumerAt t h =
  Static.directedSelectedWeight (fineGraphAt t h)

-- Exact recovery: at EVERY time, equality of retained history
-- implies equality of the original selected directed-edge consumer.
historicalConsumerRecovery :
  (t : HistoryTime) ->
  Consumer.ConsumerSufficient retainedObserver (selectedConsumerAt t)
historicalConsumerRecovery t left right same =
  cong (selectedConsumerAt t) (proj₂ same)

historicalConsumerResidualRepair :
  (t : HistoryTime) ->
  Consumer.ResidualRepair coarseHistory
    (λ h -> h) (selectedConsumerAt t)
historicalConsumerResidualRepair t = record
  { jointSufficient = historicalConsumerRecovery t }

-- An explicit compatible history evolution may update the states.
-- This generic law expresses the right consumer-relative dynamical
-- observability theorem: if complete histories coincide, so do
-- their observed consumers after any common deterministic update.
historicalEvolutionConsumerRecovery :
  (step : RetainedGraphHistory -> RetainedGraphHistory) ->
  (t : HistoryTime) ->
  (left right : RetainedGraphHistory) ->
  retainedObserver left ≡ retainedObserver right ->
  selectedConsumerAt t (step left)
    ≡ selectedConsumerAt t (step right)
historicalEvolutionConsumerRecovery step t left right same =
  cong (λ h -> selectedConsumerAt t (step h)) (proj₂ same)

-- Generic history-aware NEGATIVE criterion. An actual no-go requires
-- an equality of the WHOLE retained-history observation, not merely
-- the C3 orbit images. No such collision is fabricated for the
-- faithful retainedObserver above.
historicalCollisionBlocksRecovery :
  {State Hist Outcome : Set} ->
  (history : State -> Hist) ->
  (consumer : State -> Outcome) ->
  (left right : State) ->
  history left ≡ history right ->
  (consumer left ≡ consumer right -> ⊥) ->
  Consumer.ConsumerSufficient history consumer -> ⊥
historicalCollisionBlocksRecovery history consumer left right same differs
    supposedlySufficient =
  differs (supposedlySufficient left right same)

-- The original STATIC C3 collision is still real, but it is *not*
-- a collision of our new complete retained history.
staticCollisionCannotBecomeFullHistoryCollision :
  Static.leftGraph ≡ Static.rightGraph -> ⊥
staticCollisionCannotBecomeFullHistoryCollision same =
  Static.selectedWeightDifferent
    (cong Static.directedSelectedWeight same)

-- The original matrix contains all nine source-target weights.
-- The graph/matrix BIDI reopens these without assuming that the
-- independently typed 18-phase block or 27-valued trit cube is a
-- representation of arbitrary Nat weights.
allNinePositionsReopen :
  (graph : Graph.WeightedDigraph3) ->
  (s t : Matrix.Participant3) ->
  Graph.matrixToDigraph (Graph.digraphToMatrix graph) s t
    ≡ graph s t
allNinePositionsReopen = Graph.digraphMatrixRoundTrip

-- Existing 9->18 and 9->27 constructions are separate typed
-- refinements. Their actual consumer-preserving intertwiners,
-- where appropriate, must be supplied for this Nat-weighted graph.
-- Thus the recovery theorem neither truncates nor confuses them.

------------------------------------------------------------------------
-- 9 -> TWO-ENDED INCIDENCE (18 roles) -> 27-CHOICE REFINEMENT.
--
-- These are THREE DIFFERENT TYPE CLAIMS, preserved independently:
--  * nine ordered source-target entries (3x3);
--  * two incidence roles for EACH entry: atSource, atTarget (18);
--  * each ternary ROW has 27 possible trit values, and the full
--    3-row matrix is a depth-3 address with 27^3 possibilities.
--
-- The distinct Fricke ModeBlock18 = BinaryPhase x Codec.Sheet9
-- is NOT falsely equated with the 18 directed incidence roles.
------------------------------------------------------------------------

sourceRoleReadsActualWeight :
  (g : Graph.WeightedDigraph3)
  (s t : Matrix.Participant3) ->
  Directed.restrictDirected
    (Directed.atSource {source = s} {target = t})
    (Orbit.rowsFor g s)
    ≡ g s t
sourceRoleReadsActualWeight g s t = refl

targetRoleReadsActualWeight :
  (g : Graph.WeightedDigraph3)
  (s t : Matrix.Participant3) ->
  Directed.restrictDirected
    (Directed.atTarget {source = s} {target = t})
    (Orbit.rowsFor g t)
    ≡ g s t
targetRoleReadsActualWeight g s t = refl

bothIncidenceRolesAgree :
  (g : Graph.WeightedDigraph3)
  (s t : Matrix.Participant3) ->
  Directed.restrictDirected
    (Directed.atSource {source = s} {target = t})
    (Orbit.rowsFor g s)
  ≡
  Directed.restrictDirected
    (Directed.atTarget {source = s} {target = t})
    (Orbit.rowsFor g t)
bothIncidenceRolesAgree g s t = refl

ternaryNineToDepthThree :
  Matrix.ObserverMatrix3 SSP.SSPTrit ->
  Hyper.TernaryAddress 3 3
ternaryNineToDepthThree = Cube.observerToDepth3Address

ternaryDepthThreeReturnsNine :
  (matrix : Matrix.ObserverMatrix3 SSP.SSPTrit) ->
  Cube.depth3AddressToObserver (ternaryNineToDepthThree matrix)
    ≡ matrix
ternaryDepthThreeReturnsNine = Cube.observerAddressRoundTrip

-- An exact finite 18-state chart EXISTS, but is not the same object
-- as the 18 incidence roles unless an explicit morphism is proved.
frickeEighteenIsExactlyEighteen :
  Mode18.modeBlockStateCount ≡ 18
frickeEighteenIsExactlyEighteen =
  Mode18.modeBlockStateCountIsEighteen

-- The wave's signed value is a consumer of the ORIGINAL directed
-- selected edge. Retaining the entire history recovers it at each
-- point, irrespective of the shape of the coarse C3 summary.
signedWaveConsumerAt :
  HistoryTime -> RetainedGraphHistory -> Wave.Trit
signedWaveConsumerAt t h =
  Static.selectedWaveTrit (fineGraphAt t h)

historicalWaveConsumerRecovery :
  (t : HistoryTime) ->
  Consumer.ConsumerSufficient retainedObserver (signedWaveConsumerAt t)
historicalWaveConsumerRecovery t left right same =
  cong (signedWaveConsumerAt t) (proj₂ same)
