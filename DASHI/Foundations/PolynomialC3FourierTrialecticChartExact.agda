module DASHI.Foundations.PolynomialC3FourierTrialecticChartExact where

------------------------------------------------------------------------
-- A GENUINE 27-cell chart: polynomial C3 label cycle -> existing phase C3,
-- then the three trialectic coordinates -> existing C3^3 Fourier cube.
--
-- Finite Fourier source owners: Terras (1999), Serre (1977), original
-- DASHI C3FourierConjugationExact and C3CubeFourier27Exact contributors.
-- No analytic polynomial branch surface, continuum Hilbert space or
-- Monster 3B same-object inference is introduced by this carrier chart.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_)

import Base369 as Base
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Synthesis
import DASHI.Algebra.TriadicDepthOneCharacters as PhaseChar
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.TernaryPermutationCyclicSubgroupsExact as Cyclic
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel
import DASHI.Biology.Physical.C3CubeFourier27Exact as Cube

phaseToCharacter :
  Phase.Phase3 → PhaseChar.C3Phase
phaseToCharacter Phase.phase0 = PhaseChar.phase0
phaseToCharacter Phase.phase1 = PhaseChar.phase1
phaseToCharacter Phase.phase2 = PhaseChar.phase2

characterToPhase :
  PhaseChar.C3Phase → Phase.Phase3
characterToPhase PhaseChar.phase0 = Phase.phase0
characterToPhase PhaseChar.phase1 = Phase.phase1
characterToPhase PhaseChar.phase2 = Phase.phase2

phaseCharacterRoundTrip :
  (p : Phase.Phase3) → characterToPhase (phaseToCharacter p) ≡ p
phaseCharacterRoundTrip Phase.phase0 = refl
phaseCharacterRoundTrip Phase.phase1 = refl
phaseCharacterRoundTrip Phase.phase2 = refl

characterPhaseRoundTrip :
  (p : PhaseChar.C3Phase) → phaseToCharacter (characterToPhase p) ≡ p
characterPhaseRoundTrip PhaseChar.phase0 = refl
characterPhaseRoundTrip PhaseChar.phase1 = refl
characterPhaseRoundTrip PhaseChar.phase2 = refl

c3ProductIntertwinesFourierPhase :
  (a b : Phase.Phase3) →
  phaseToCharacter (Cyclic._+₃_ a b)
  ≡ PhaseChar.multiplyPhase (phaseToCharacter a) (phaseToCharacter b)
c3ProductIntertwinesFourierPhase Phase.phase0 Phase.phase0 = refl
c3ProductIntertwinesFourierPhase Phase.phase0 Phase.phase1 = refl
c3ProductIntertwinesFourierPhase Phase.phase0 Phase.phase2 = refl
c3ProductIntertwinesFourierPhase Phase.phase1 Phase.phase0 = refl
c3ProductIntertwinesFourierPhase Phase.phase1 Phase.phase1 = refl
c3ProductIntertwinesFourierPhase Phase.phase1 Phase.phase2 = refl
c3ProductIntertwinesFourierPhase Phase.phase2 Phase.phase0 = refl
c3ProductIntertwinesFourierPhase Phase.phase2 Phase.phase1 = refl
c3ProductIntertwinesFourierPhase Phase.phase2 Phase.phase2 = refl

c3FourierConjugateRows :
  Fourier.conjugateRow Fourier.chi1 ≡ Fourier.chi2
c3FourierConjugateRows = Fourier.chi1ConjugateIsChi2

truthToWheel :
  Base.TriTruth → Wheel.DepthWheelPhase
truthToWheel Base.tri-low = Wheel.phase-0
truthToWheel Base.tri-mid = Wheel.phase-1
truthToWheel Base.tri-high = Wheel.phase-2

wheelToTruth :
  Wheel.DepthWheelPhase → Base.TriTruth
wheelToTruth Wheel.phase-0 = Base.tri-low
wheelToTruth Wheel.phase-1 = Base.tri-mid
wheelToTruth Wheel.phase-2 = Base.tri-high

wheelTruthRoundTrip :
  (p : Wheel.DepthWheelPhase) →
  truthToWheel (wheelToTruth p) ≡ p
wheelTruthRoundTrip Wheel.phase-0 = refl
wheelTruthRoundTrip Wheel.phase-1 = refl
wheelTruthRoundTrip Wheel.phase-2 = refl

truthWheelRoundTrip :
  (t : Base.TriTruth) →
  wheelToTruth (truthToWheel t) ≡ t
truthWheelRoundTrip Base.tri-low = refl
truthWheelRoundTrip Base.tri-mid = refl
truthWheelRoundTrip Base.tri-high = refl

toFourierCube :
  Synthesis.SynthesisChoice27 → Cube.Cube3
toFourierCube (x , (y , z)) =
  Cube.cube3 (truthToWheel x) (truthToWheel y) (truthToWheel z)

fromFourierCube :
  Cube.Cube3 → Synthesis.SynthesisChoice27
fromFourierCube (Cube.cube3 x y z) =
  wheelToTruth x , (wheelToTruth y , wheelToTruth z)

synthesisFourierRoundTrip :
  (s : Synthesis.SynthesisChoice27) →
  fromFourierCube (toFourierCube s) ≡ s
synthesisFourierRoundTrip (x , (y , z))
  rewrite truthWheelRoundTrip x
        | truthWheelRoundTrip y
        | truthWheelRoundTrip z = refl

fourierSynthesisRoundTrip :
  (cube : Cube.Cube3) →
  toFourierCube (fromFourierCube cube) ≡ cube
fourierSynthesisRoundTrip (Cube.cube3 x y z)
  rewrite wheelTruthRoundTrip x
        | wheelTruthRoundTrip y
        | wheelTruthRoundTrip z = refl

-- This is a direct transport of an EXISTING C3^3 group character law.
cubeCharacterHomomorphismReused :
  (k x y : Cube.Cube3) →
  Cube.character k (Cube.cubeAdd x y)
  ≡ Cube.cubeAdd (Cube.character k x) (Cube.character k y)
cubeCharacterHomomorphismReused =
  Cube.cubeCharacterHomomorphism
