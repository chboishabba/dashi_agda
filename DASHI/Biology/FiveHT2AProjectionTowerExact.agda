module DASHI.Biology.FiveHT2AProjectionTowerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.QuotientResidualCategoricalLoom as Loom
import DASHI.Biology.FiveHT2ARecognitionResidualProjectionExact as Recognition
import DASHI.Biology.FiveHT2ASignalingDialecticExact as Signaling
import DASHI.Cognition.KlueverFormConstantProjection as Kluver

------------------------------------------------------------------------
-- RECOGNITION -> SIGNALING -> CIRCUIT/PUBLIC -> PERCEPT PROJECTION TOWER
--
-- The tower is intentionally many-to-one.  It is a repo-native categorical
-- loom over ordinary Set projections, not a claim that every biological arrow
-- is a functor with empirically validated dynamics.
------------------------------------------------------------------------

data SignalingSurface : Set where
  lsdSignalingSurface : SignalingSurface

data CircuitSurface : Set where
  alteredCircuitCandidate : CircuitSurface

data PerceptSurface : Set where
  unresolvedPercept : PerceptSurface

recognitionToSignaling :
  Recognition.RecognitionMicroState →
  SignalingSurface
recognitionToSignaling Recognition.lsdState0 = lsdSignalingSurface
recognitionToSignaling Recognition.lsdState1 = lsdSignalingSurface

signalingToCircuit :
  SignalingSurface →
  CircuitSurface
signalingToCircuit lsdSignalingSurface = alteredCircuitCandidate

circuitToPercept :
  CircuitSurface →
  PerceptSurface
circuitToPercept alteredCircuitCandidate = unresolvedPercept

recognitionToCircuit :
  Recognition.RecognitionMicroState →
  CircuitSurface
recognitionToCircuit state =
  signalingToCircuit (recognitionToSignaling state)

recognitionToPercept :
  Recognition.RecognitionMicroState →
  PerceptSurface
recognitionToPercept state =
  circuitToPercept (recognitionToCircuit state)

------------------------------------------------------------------------
-- Exact composition laws.
------------------------------------------------------------------------

recognitionCircuitComposition :
  (state : Recognition.RecognitionMicroState) →
  recognitionToCircuit state
  ≡
  signalingToCircuit (recognitionToSignaling state)
recognitionCircuitComposition state = refl

recognitionPerceptComposition :
  (state : Recognition.RecognitionMicroState) →
  recognitionToPercept state
  ≡
  circuitToPercept
    (signalingToCircuit
      (recognitionToSignaling state))
recognitionPerceptComposition state = refl

------------------------------------------------------------------------
-- Many-to-one witnesses.
------------------------------------------------------------------------

recognitionStatesCollapseAtSignaling :
  recognitionToSignaling Recognition.lsdState0
  ≡
  recognitionToSignaling Recognition.lsdState1
recognitionStatesCollapseAtSignaling = refl

recognitionStatesCollapseAtCircuit :
  recognitionToCircuit Recognition.lsdState0
  ≡
  recognitionToCircuit Recognition.lsdState1
recognitionStatesCollapseAtCircuit = refl

recognitionStatesCollapseAtPercept :
  recognitionToPercept Recognition.lsdState0
  ≡
  recognitionToPercept Recognition.lsdState1
recognitionStatesCollapseAtPercept = refl

recognitionStatesRemainDistinct :
  Recognition.lsdState0 ≡ Recognition.lsdState1 → ⊥
recognitionStatesRemainDistinct =
  Recognition.distinctMicrostates

------------------------------------------------------------------------
-- Categorical loom objects / arrows.
------------------------------------------------------------------------

recognitionObject : Loom.SetProjectionObject
recognitionObject =
  Loom.setProjectionObject Recognition.RecognitionMicroState

signalingObject : Loom.SetProjectionObject
signalingObject =
  Loom.setProjectionObject SignalingSurface

circuitObject : Loom.SetProjectionObject
circuitObject =
  Loom.setProjectionObject CircuitSurface

perceptObject : Loom.SetProjectionObject
perceptObject =
  Loom.setProjectionObject PerceptSurface

recognitionSignalingHom :
  Loom.SetProjectionHom recognitionObject signalingObject
recognitionSignalingHom =
  Loom.setProjectionHom recognitionToSignaling

signalingCircuitHom :
  Loom.SetProjectionHom signalingObject circuitObject
signalingCircuitHom =
  Loom.setProjectionHom signalingToCircuit

circuitPerceptHom :
  Loom.SetProjectionHom circuitObject perceptObject
circuitPerceptHom =
  Loom.setProjectionHom circuitToPercept

recognitionCircuitHom :
  Loom.SetProjectionHom recognitionObject circuitObject
recognitionCircuitHom =
  Loom.setProjectionCompose
    signalingCircuitHom
    recognitionSignalingHom

recognitionPerceptHom :
  Loom.SetProjectionHom recognitionObject perceptObject
recognitionPerceptHom =
  Loom.setProjectionCompose
    circuitPerceptHom
    recognitionCircuitHom

------------------------------------------------------------------------
-- Existing signaling / Kluever vocabularies remain external owners.
------------------------------------------------------------------------

signalingDialectic :
  Signaling.FiveHT2ASignalingDialectic
signalingDialectic =
  Signaling.canonicalFiveHT2ASignalingDialectic

targetKluverForms : List Kluver.KlueverForm
targetKluverForms =
  Kluver.latticeGrating
  ∷ Kluver.tunnelFunnel
  ∷ Kluver.spiral
  ∷ Kluver.radialCobweb
  ∷ []

------------------------------------------------------------------------
-- Non-faithfulness / inverse-blocking.
------------------------------------------------------------------------

data SignalingProjectionFaithfullyRecoversRecognition : Set where
data CircuitProjectionFaithfullyRecoversRecognition : Set where
data PerceptProjectionFaithfullyRecoversRecognition : Set where
data PerceptDeterminesLigand : Set where

signalingProjectionNotFaithful :
  SignalingProjectionFaithfullyRecoversRecognition → ⊥
signalingProjectionNotFaithful ()

circuitProjectionNotFaithful :
  CircuitProjectionFaithfullyRecoversRecognition → ⊥
circuitProjectionNotFaithful ()

perceptProjectionNotFaithful :
  PerceptProjectionFaithfullyRecoversRecognition → ⊥
perceptProjectionNotFaithful ()

perceptDoesNotDetermineLigand :
  PerceptDeterminesLigand → ⊥
perceptDoesNotDetermineLigand ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record FiveHT2AProjectionTowerBoundary : Set where
  constructor fiveHT2AProjectionTowerBoundary
  field
    projectionCompositionIsExact : Bool
    projectionCompositionIsExactIsTrue :
      projectionCompositionIsExact ≡ true

    recognitionToSignalingCanBeManyToOne : Bool
    recognitionToSignalingCanBeManyToOneIsTrue :
      recognitionToSignalingCanBeManyToOne ≡ true

    signalingToCircuitIsCalibratedMechanisticMap : Bool
    signalingToCircuitIsCalibratedMechanisticMapIsFalse :
      signalingToCircuitIsCalibratedMechanisticMap ≡ false

    circuitToPerceptIsCalibratedMechanisticMap : Bool
    circuitToPerceptIsCalibratedMechanisticMapIsFalse :
      circuitToPerceptIsCalibratedMechanisticMap ≡ false

    downstreamSurfaceSupportsUniqueInverse : Bool
    downstreamSurfaceSupportsUniqueInverseIsFalse :
      downstreamSurfaceSupportsUniqueInverse ≡ false

open FiveHT2AProjectionTowerBoundary public

canonicalFiveHT2AProjectionTowerBoundary :
  FiveHT2AProjectionTowerBoundary
canonicalFiveHT2AProjectionTowerBoundary =
  fiveHT2AProjectionTowerBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
