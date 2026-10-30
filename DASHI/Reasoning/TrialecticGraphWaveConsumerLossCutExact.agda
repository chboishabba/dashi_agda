module DASHI.Reasoning.TrialecticGraphWaveConsumerLossCutExact where

------------------------------------------------------------------------
-- MATRIX/GRAPH/WAVE CONSUMER-LOSS MAX-CUT (30 October 2026).
--
-- SOURCE OWNERS / ATTRIBUTION
-- Standard matrix/digraph equivalence and finite cyclic averaging are
-- classical. The 2026-10-26 Tivadar Danka illustration prompts the
-- matrix chart; it does not own these classical theorems.
-- Original graph owners (PR #1438): TrialecticWeightedDirectedGraph369Exact,
-- TrialecticC3WeightedOrbitSymmetrizationExact, typed source/target fabric.
-- Original wave owner: Physics.WaveAlgorithmLift / WaveRefinementTower.
-- Consumer-indexed refinement: Core.ConsumerIndexedResidualRefinementExact
-- (Blackwell 1953; Cousot-Cousot 1977 as method precedents).
--
-- This is a CONCRETE collision in actual C3-averaged GRAPH WEIGHTS:
--   one live A->B edge vs one live B->C edge.
-- Their 3x3 C3 orbit-sum matrices coincide, but the directed
-- A->B signed/wave consumer differs.
--
-- A downstream wave stage USING ONLY the averaged graph cannot
-- recover that lost consumer. A full ordered directed matrix can.
-- This does not identify graph edges with prime pairs or Pickover
-- circle phases. Arithmetic/analytic producers remain obligatory.
--
-- Source-written, Agda kernel pending; never claim that a finite
-- graph/shift/interference bound proves twin-prime infinitude,
-- a phase-digit at 9999!, or a Monster same-object theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Reasoning.TrialecticWeightedDirectedGraph369Exact as Graph
import DASHI.Reasoning.TrialecticC3WeightedOrbitSymmetrizationExact as Orbit
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Reasoning.TypedHyperfabricCore as Fabric
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Refine
import DASHI.Physics.WaveAlgorithmLift as Wave

-- The first graph marks exactly the directed A->B edge.
-- The second marks its C3 translate B->C, not a reverse edge.
leftGraph : Graph.WeightedDigraph3
leftGraph Observer.participantA Observer.participantB = 1
leftGraph _ _ = 0

rightGraph : Graph.WeightedDigraph3
rightGraph Observer.participantB Observer.participantC = 1
rightGraph _ _ = 0

-- Reuse exact graph/matrix BIDI and the source-owned C3 orbit sum.
orbitMatrix : Graph.WeightedDigraph3 -> Graph.WeightedMatrix3
orbitMatrix g = Graph.digraphToMatrix (Orbit.orbitSum g)

-- The same C3-symmetrised weighted adjacency matrix. This is an
-- actual 9-entry *data* equality, not function extensionality.
sameOrbitMatrix :
  orbitMatrix leftGraph ≡ orbitMatrix rightGraph
sameOrbitMatrix = refl

directedSelectedWeight : Graph.WeightedDigraph3 -> Nat
directedSelectedWeight g =
  g Observer.participantA Observer.participantB

leftSelectedWeightIsOne :
  directedSelectedWeight leftGraph ≡ 1
leftSelectedWeightIsOne = refl

rightSelectedWeightIsZero :
  directedSelectedWeight rightGraph ≡ 0
rightSelectedWeightIsZero = refl

selectedWeightDifferent :
  directedSelectedWeight leftGraph
  ≡ directedSelectedWeight rightGraph -> ⊥
selectedWeightDifferent ()

graphOrbitConsumerCollision :
  Refine.ConsumerRelevantCollision
    orbitMatrix directedSelectedWeight
graphOrbitConsumerCollision = record
  { left = leftGraph
  ; right = rightGraph
  ; sameSurface = sameOrbitMatrix
  ; differentOutcome = selectedWeightDifferent
  }

-- The correct original (directed matrix) observer retains the
-- consumer: graphToMatrix roundtrip allows reading source/target
-- weight without any automorphism or wave theorem.
unaveragedMatrixConsumer :
  Graph.WeightedMatrix3 -> Nat
unaveragedMatrixConsumer m =
  Graph.matrixToDigraph m
    Observer.participantA Observer.participantB

unaveragedMatrixReadsSelected :
  (g : Graph.WeightedDigraph3) ->
  unaveragedMatrixConsumer (Graph.digraphToMatrix g)
    ≡ directedSelectedWeight g
unaveragedMatrixReadsSelected g =
  Graph.digraphMatrixRoundTrip g
    Observer.participantA Observer.participantB

-- NO graph-symmetrised observer can recover the actual A->B weight
-- for all directed graphs. It fails on explicit supported states.
orbitOnlyCannotRecoverSelectedWeight :
  Refine.ConsumerSufficient orbitMatrix directedSelectedWeight -> ⊥
orbitOnlyCannotRecoverSelectedWeight =
  Refine.coarseCollisionBlocksSufficiency
    graphOrbitConsumerCollision

-- No arbitrary extra computation, including a wave evolution or
-- spectrum, can restore erased source/target information if it is
-- fed ONLY the C3-averaged adjacency matrix. This is a generic
-- deterministic consumer-factoring no-go theorem.
noWavePostprocessCanRepairErasedOrbit :
  {WaveOutput : Set} ->
  (liftOrEvolve : Graph.WeightedMatrix3 -> WaveOutput) ->
  (readout : WaveOutput -> Nat) ->
  ((g : Graph.WeightedDigraph3) ->
    readout (liftOrEvolve (orbitMatrix g))
      ≡ directedSelectedWeight g) -> ⊥
noWavePostprocessCanRepairErasedOrbit evolve readout correct =
  selectedWeightDifferent
    (trans
      (sym (correct leftGraph))
      (trans
        (cong (λ m -> readout (evolve m)) sameOrbitMatrix)
        (correct rightGraph)))

------------------------------------------------------------------------
-- The source wave calculus uses a 3-valued trit and an EXACT finite
-- encoding. We attach only the local signed observable, not a
-- fabricated Hilbert/spectral phase or a prime-correlation weight.
------------------------------------------------------------------------

selectedWaveTrit : Graph.WeightedDigraph3 -> Wave.Trit
selectedWaveTrit g with Graph.presentWeight (directedSelectedWeight g)
... | true = Wave.pos
... | false = Wave.zero

leftSelectedWavePositive : selectedWaveTrit leftGraph ≡ Wave.pos
leftSelectedWavePositive = refl

rightSelectedWaveZero : selectedWaveTrit rightGraph ≡ Wave.zero
rightSelectedWaveZero = refl

waveTritOutcomesDiffer :
  selectedWaveTrit leftGraph ≡ selectedWaveTrit rightGraph -> ⊥
waveTritOutcomesDiffer ()

waveConsumerNonDescent :
  Refine.ConsumerRelevantCollision orbitMatrix selectedWaveTrit
waveConsumerNonDescent = record
  { left = leftGraph
  ; right = rightGraph
  ; sameSurface = sameOrbitMatrix
  ; differentOutcome = waveTritOutcomesDiffer
  }

waveTritNotRecoverableFromOrbit :
  Refine.ConsumerSufficient orbitMatrix selectedWaveTrit -> ⊥
waveTritNotRecoverableFromOrbit =
  Refine.coarseCollisionBlocksSufficiency
    waveConsumerNonDescent

-- Both directed graphs STILL admit global compatible sections of
-- the inherited source/target TypedHyperfabric. Compatibility of
-- gluing itself does not restore the orientation discarded by C3.
leftDirectedSection :
  Fabric.GlobalSection (Orbit.directedFabricFor leftGraph)
leftDirectedSection = Orbit.compatibleSectionFor leftGraph

rightDirectedSection :
  Fabric.GlobalSection (Orbit.directedFabricFor rightGraph)
rightDirectedSection = Orbit.compatibleSectionFor rightGraph

-- The actual WaveRefinementTower type in WaveAlgorithmLift requires
-- project/evolution/observation commutation. No such analytic
-- instance on actual shifted-prime correlations or circle phase
-- was constructed in this finite example.
