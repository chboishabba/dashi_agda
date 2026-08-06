module DASHI.Biology.StateDependentMultiplexTransducer where

open import DASHI.Core.Prelude

import DASHI.Biology.Core.ContextIndexedSystem as Context
import DASHI.Biology.Cell.BioelectricNetwork as Bioelectric

------------------------------------------------------------------------
-- State-dependent neural computation over a network of networks.
--
-- The carrier is deliberately stronger than y = phi (W x + b): a local
-- processor consumes an input, its prior state, and a modulatory context,
-- then returns both an output and a successor state.  The same physical input
-- may therefore be transmitted, suppressed, inverted, or routed differently
-- without changing the input token itself.
--
-- Source-facing references:
--
-- David Beniaguev, Idan Segev, Michael London,
-- "Single cortical neurons as deep artificial neural networks",
-- DOI 10.1016/j.neuron.2021.07.002.
--
-- Michael London, Michael Hausser, "Dendritic computation",
-- DOI 10.1146/annurev.neuro.28.061604.135703.

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

data CouplingArity : Set where
  oneToOneCoupling : CouplingArity
  oneToManyCoupling : CouplingArity
  manyToOneCoupling : CouplingArity
  manyToManyCoupling : CouplingArity
  contextIndexedCoupling : CouplingArity
  stateTransformingCoupling : CouplingArity

data MultiplexLayer : Set where
  axonalLayer : MultiplexLayer
  synapticLayer : MultiplexLayer
  dendriticLayer : MultiplexLayer
  chemicalLayer : MultiplexLayer
  oscillatoryLayer : MultiplexLayer
  metabolicLayer : MultiplexLayer
  functionalLayer : MultiplexLayer

record StatefulTransducer : Set₁ where
  field
    Input : Set
    State : Set
    Modulator : Set
    Output : Set

    step :
      Input → State → Modulator →
      Output × State

open StatefulTransducer public

runOutput :
  (T : StatefulTransducer) →
  Input T → State T → Modulator T → Output T
runOutput T x s m =
  proj₁ (step T x s m)

runState :
  (T : StatefulTransducer) →
  Input T → State T → Modulator T → State T
runState T x s m =
  proj₂ (step T x s m)

record MultiplexTransducerNode : Set₁ where
  constructor multiplexTransducerNode
  field
    nodeLabel : MultiplexLayer
    nodeArity : CouplingArity
    nodeTransducer : StatefulTransducer

open MultiplexTransducerNode public

boolNot : Bool → Bool
boolNot false = true
boolNot true = false

xor : Bool → Bool → Bool
xor false false = false
xor false true = true
xor true false = true
xor true true = false

boolNotInvolutive :
  (x : Bool) →
  boolNot (boolNot x) ≡ x
boolNotInvolutive false = refl
boolNotInvolutive true = refl

false≢true : false ≢ true
false≢true ()

true≢false : true ≢ false
true≢false ()

------------------------------------------------------------------------
-- A concrete deterministic stateful transducer.
--
-- output = input xor prior-state xor modulator
-- state' = prior-state xor modulator
--
-- The model is intentionally finite.  It proves the structural point without
-- pretending that Bool is a biophysical neuron.

canonicalBoolTransducer : StatefulTransducer
canonicalBoolTransducer =
  record
    { Input = Bool
    ; State = Bool
    ; Modulator = Bool
    ; Output = Bool
    ; step = λ x s m → xor (xor x s) m , xor s m
    }

canonicalDendriticNode : MultiplexTransducerNode
canonicalDendriticNode =
  multiplexTransducerNode
    dendriticLayer
    manyToOneCoupling
    canonicalBoolTransducer

canonicalStateChangesOutput :
  runOutput canonicalBoolTransducer false false false
  ≢
  runOutput canonicalBoolTransducer false true false
canonicalStateChangesOutput =
  false≢true

canonicalModulatorChangesOutput :
  runOutput canonicalBoolTransducer true false false
  ≢
  runOutput canonicalBoolTransducer true false true
canonicalModulatorChangesOutput =
  true≢false

canonicalModulatorChangesSuccessorState :
  runState canonicalBoolTransducer false false true ≡ true
canonicalModulatorChangesSuccessorState =
  refl

canonicalUnmodulatedStatePersists :
  runState canonicalBoolTransducer true true false ≡ true
canonicalUnmodulatedStatePersists =
  refl

------------------------------------------------------------------------
-- Existing DASHI context-indexed and bioelectric carriers are instantiated,
-- rather than replaced by a parallel neural ontology.

canonicalContextIndexedProjection :
  Context.ContextIndexedProjection
canonicalContextIndexedProjection =
  record
    { Hidden = Bool
    ; Context = Bool
    ; Observable = Bool
    ; project = λ context hidden → xor context hidden
    }

canonicalProjectionDependsOnContext :
  Context.ContextIndexedProjection.project
    canonicalContextIndexedProjection false false
  ≢
  Context.ContextIndexedProjection.project
    canonicalContextIndexedProjection true false
canonicalProjectionDependsOnContext =
  false≢true

canonicalBioelectricNetwork :
  Bioelectric.BioelectricNetwork
canonicalBioelectricNetwork =
  record
    { Node = Bool
    ; Voltage = Bool
    ; Conductance = Bool
    ; Current = Bool
    ; ChannelState = Bool
    ; GapJunctionState = Bool
    ; ChemicalSignal = Bool
    ; MechanicalState = Bool
    ; RegulatoryState = Bool
    ; NetworkState = Bool
    ; Environment = Bool
    ; voltageAt = λ networkState node → xor networkState node
    ; coupling = λ networkState source target →
        xor networkState (xor source target)
    ; ionicCurrent = λ networkState node → xor networkState node
    ; channelState = λ networkState node → xor networkState node
    ; gapJunction = λ networkState source target →
        xor networkState (xor source target)
    ; update = λ environment chemical mechanical regulatory networkState →
        xor environment
          (xor chemical
            (xor mechanical
              (xor regulatory networkState)))
    }

canonicalBioelectricChemicalModulation :
  Bioelectric.BioelectricNetwork.update
    canonicalBioelectricNetwork
    false false false false false
  ≢
  Bioelectric.BioelectricNetwork.update
    canonicalBioelectricNetwork
    false true false false false
canonicalBioelectricChemicalModulation =
  false≢true

record StateDependentMultiplexBoundary : Set where
  constructor stateDependentMultiplexBoundary
  field
    vectorsAreLocalCoordinates : Bool
    vectorsAreLocalCoordinatesIsTrue :
      vectorsAreLocalCoordinates ≡ true

    fixedGraphIsCompleteBrainModel : Bool
    fixedGraphIsCompleteBrainModelIsFalse :
      fixedGraphIsCompleteBrainModel ≡ false

    neuronIsTimelessScalarActivation : Bool
    neuronIsTimelessScalarActivationIsFalse :
      neuronIsTimelessScalarActivation ≡ false

    deterministicMicroModelPromotedAsCompleteBrain : Bool
    deterministicMicroModelPromotedAsCompleteBrainIsFalse :
      deterministicMicroModelPromotedAsCompleteBrain ≡ false

canonicalStateDependentMultiplexBoundary :
  StateDependentMultiplexBoundary
canonicalStateDependentMultiplexBoundary =
  stateDependentMultiplexBoundary
    true refl
    false refl
    false refl
    false refl
