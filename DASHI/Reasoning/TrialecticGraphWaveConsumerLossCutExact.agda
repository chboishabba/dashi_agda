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

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (proj₂)
import DASHI.Core.ObserverRefinementLatticeExact as ObserverRefinement
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_+_ to _+ℤ_)
import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
import DASHI.Physics.ShiftUnitaryLikeConstraint as SULC

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

------------------------------------------------------------------------
-- C4 / QUARTER-TURN WAVE: POSITIVE SPECTRAL ENERGY DOES NOT FORCE
-- POSITIVE TWO-POINT CORRELATION.
--
-- The genuine integer shifted-prime correlation is at lag TWO.
-- The original DASHI wave module has a cyclic quarter-turn mulI
-- (Gaussian integer pairs), not a full analytic Fourier theory.
-- Here a FOUR-site finite counterexample uses the same carrier and
-- exact norms. This is a discrete Fourier identity, not a statement
-- that the artificial f has anything to do with real von Mangoldt.
--
-- f=(1,1,0,0) on the four-cycle has total positive mass TWO, but
-- sum_{j mod 4} f(j)f(j+2)=0.
-- Its Gaussian Fourier modes are (2,1-i,0,1+i), norms 4,2,0,2.
-- The lag-two spectral multiplier is (-1)^k. Thus the exact
-- signed spectral numerator is 4-2+0-2=0, even though every
-- individual norm-square is nonnegative.
--
-- Consequently, a Hilbert/spectral-mode norm or a graph's positive
-- energy alone cannot guarantee a nonzero +2 arithmetic correlation.
-- Actual prime-specific distribution estimates are indispensable.
------------------------------------------------------------------------

data FourSite : Set where
  siteZero siteOne siteTwo siteThree : FourSite

lagTwoSite : FourSite -> FourSite
lagTwoSite siteZero = siteTwo
lagTwoSite siteOne = siteThree
lagTwoSite siteTwo = siteZero
lagTwoSite siteThree = siteOne

positiveMassCounterfeit : FourSite -> Nat
positiveMassCounterfeit siteZero = 1
positiveMassCounterfeit siteOne = 1
positiveMassCounterfeit siteTwo = 0
positiveMassCounterfeit siteThree = 0

counterfeitTotalMass :
  positiveMassCounterfeit siteZero
  + positiveMassCounterfeit siteOne
  + positiveMassCounterfeit siteTwo
  + positiveMassCounterfeit siteThree
  ≡ 2
counterfeitTotalMass = refl

counterfeitLagTwoCorrelation : Nat
counterfeitLagTwoCorrelation =
  positiveMassCounterfeit siteZero
    * positiveMassCounterfeit (lagTwoSite siteZero)
  + positiveMassCounterfeit siteOne
    * positiveMassCounterfeit (lagTwoSite siteOne)
  + positiveMassCounterfeit siteTwo
    * positiveMassCounterfeit (lagTwoSite siteTwo)
  + positiveMassCounterfeit siteThree
    * positiveMassCounterfeit (lagTwoSite siteThree)

counterfeitLagTwoIsZero : counterfeitLagTwoCorrelation ≡ 0
counterfeitLagTwoIsZero = refl

gaussianFourierZero : SDWS.DiscreteWave
gaussianFourierZero = SDWS.mkDiscreteWave (+ 2) (+ 0)

gaussianFourierOne : SDWS.DiscreteWave
gaussianFourierOne = SDWS.mkDiscreteWave (+ 1) (-[1+ 0 ])

gaussianFourierTwo : SDWS.DiscreteWave
gaussianFourierTwo = SDWS.mkDiscreteWave (+ 0) (+ 0)

gaussianFourierThree : SDWS.DiscreteWave
gaussianFourierThree = SDWS.mkDiscreteWave (+ 1) (+ 1)

fourierZeroEnergy : SULC.waveNormSq gaussianFourierZero ≡ + 4
fourierZeroEnergy = refl

fourierOneEnergy : SULC.waveNormSq gaussianFourierOne ≡ + 2
fourierOneEnergy = refl

fourierTwoEnergy : SULC.waveNormSq gaussianFourierTwo ≡ + 0
fourierTwoEnergy = refl

fourierThreeEnergy : SULC.waveNormSq gaussianFourierThree ≡ + 2
fourierThreeEnergy = refl

-- This is the real part of the FOURIER shift-by-two spectral sum.
-- The earlier wave norm theorem justifies each energy as an exact
-- Gaussian-integer squared norm, while the lag-two multiplier
-- contributes signs; it is NOT all-positive.
lagTwoSignedSpectralNumerator : ℤ
lagTwoSignedSpectralNumerator =
  (+ 4 +ℤ (-[1+ 1 ]))
  +ℤ ((+ 0) +ℤ (-[1+ 1 ]))

lagTwoSignedSpectralNumeratorZero :
  lagTwoSignedSpectralNumerator ≡ + 0
lagTwoSignedSpectralNumeratorZero = refl

-- Positive total density plus positive spectral magnitudes does
-- not supply a positive off-diagonal (+2) arithmetic correlation.
-- The example is deliberately synthetic, and therefore is only a
-- fail-fast countermodel to an UNSUPPORTED generic inference.

------------------------------------------------------------------------
-- POSITIVE CLOSURE: UNAVERAGED DIRECTED GRAPH IS THE SUFFICIENT
-- RESIDUAL FOR ITS SELECTED DIRECTED-EDGE CONSUMER.
--
-- This closes both halves of the real consumer-indexed refinement:
-- the C3 orbit alone is INSUFFICIENT, but retaining the original 3x3
-- matrix makes the paired observer sufficient. Moreover it is a
-- STRICT refinement, witnessed by the original C3 collision.
--
-- This is more than exhibiting an arbitrary info-loss example:
-- it constructs the actual repaired fibre via the existing core
-- rather than merely recommending to keep extra information.
------------------------------------------------------------------------

fullDirectedMatrixResidualRepair :
  Refine.ResidualRepair
    orbitMatrix
    Graph.digraphToMatrix
    directedSelectedWeight
fullDirectedMatrixResidualRepair = record
  { jointSufficient = λ left right samePair ->
      trans
        (sym (unaveragedMatrixReadsSelected left))
        (trans
          (cong unaveragedMatrixConsumer (proj₂ samePair))
          (unaveragedMatrixReadsSelected right))
  }

fullDirectedMatrixStrictlyRefinesC3Orbit :
  ObserverRefinement.StrictRefinement
    orbitMatrix
    (ObserverRefinement.pairObserver orbitMatrix Graph.digraphToMatrix)
fullDirectedMatrixStrictlyRefinesC3Orbit =
  Refine.consumerRelevantResidualGivesStrictRefinement
    graphOrbitConsumerCollision
    fullDirectedMatrixResidualRepair

-- The same retained full directed graph is sufficient for the WAVE
-- trit consumer; it preserves the selected edge's magnitude as well
-- as the positive/zero wave sign, unlike a bare C3 orbit average.
fullDirectedMatrixWaveResidualRepair :
  Refine.ResidualRepair
    orbitMatrix
    Graph.digraphToMatrix
    selectedWaveTrit
fullDirectedMatrixWaveResidualRepair = record
  { jointSufficient = λ left right samePair ->
      cong
        (λ weight -> WaveState weight)
        (trans
          (sym (unaveragedMatrixReadsSelected left))
          (trans
            (cong unaveragedMatrixConsumer (proj₂ samePair))
            (unaveragedMatrixReadsSelected right)))
  }
  where
    WaveState : Nat -> Wave.Trit
    WaveState n with Graph.presentWeight n
    ... | true = Wave.pos
    ... | false = Wave.zero
