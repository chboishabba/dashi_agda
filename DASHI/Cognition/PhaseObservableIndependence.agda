module DASHI.Cognition.PhaseObservableIndependence where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Unit using (tt)

import DASHI.Cognition.CognitiveVacuumClassBoundary as Fixture
import DASHI.Cognition.DashiCognitiveSystem as Cognitive

------------------------------------------------------------------------
-- The four observables are deliberately not collapsed into one scalar.
-- This finite fixture proves that equal branching can coexist with different
-- stack depth and different MDL slope.
------------------------------------------------------------------------

emptyStackConfig : Cognitive.Configuration Fixture.booleanCognitiveSystem
emptyStackConfig = Cognitive.configuration false []

oneObligationConfig : Cognitive.Configuration Fixture.booleanCognitiveSystem
oneObligationConfig = Cognitive.configuration false (tt ∷ [])

emptyObservation : Cognitive.PhaseObservables
emptyObservation =
  Cognitive.observePhase
    Fixture.booleanCognitiveSystem
    tt
    3
    emptyStackConfig
    0
    2

obligatedObservation : Cognitive.PhaseObservables
obligatedObservation =
  Cognitive.observePhase
    Fixture.booleanCognitiveSystem
    tt
    3
    oneObligationConfig
    0
    5

sameFeasibleBranching :
  Cognitive.PhaseObservables.feasibleBranching emptyObservation
  ≡ Cognitive.PhaseObservables.feasibleBranching obligatedObservation
sameFeasibleBranching = refl

emptyBranchingIsThree :
  Cognitive.PhaseObservables.feasibleBranching emptyObservation ≡ 3
emptyBranchingIsThree = refl

emptyStackDepthIsZero :
  Cognitive.PhaseObservables.openObligationDepth emptyObservation ≡ 0
emptyStackDepthIsZero = refl

obligatedStackDepthIsOne :
  Cognitive.PhaseObservables.openObligationDepth obligatedObservation ≡ 1
obligatedStackDepthIsOne = refl

emptyMDLRiseIsTwo :
  Cognitive.MDLFiniteDifference.rise
    (Cognitive.PhaseObservables.mdlSlope emptyObservation)
  ≡ 2
emptyMDLRiseIsTwo = refl

obligatedMDLRiseIsFive :
  Cognitive.MDLFiniteDifference.rise
    (Cognitive.PhaseObservables.mdlSlope obligatedObservation)
  ≡ 5
obligatedMDLRiseIsFive = refl

bothRemainProductive :
  Cognitive.PhaseObservables.languagePhase emptyObservation
  ≡ Cognitive.productivePhase
bothRemainProductive = refl
