module DASHI.Culture.GoodmanSonicWarfareTransportExact where

------------------------------------------------------------------------
-- SONIC SOURCE / ENVIRONMENT / OBSERVER: FINITE NON-INVERTIBILITY
--
-- Steve Goodman, Sonic Warfare (MIT Press, 2009; printed 2010 CIP),
-- DOI: 10.7551/mitpress/7999.001.0001, esp. chapters 8, 14, 15, 34.
--
-- Reuse-only general owners:
--   DASHI.Physics.ObserverConditionedTransportBridge
--   DASHI.Core.QueryIndexedProjectionAdequacyExact
--
-- This is a deliberately finite, binary abstraction of attenuation.
-- "Absorbing" is not a frequency-independent real material model.
-- No wave equation, acoustic calibration, radiation pressure, biological
-- response, scattering computation or field-equivalence is proved.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.ObserverConditionedTransportBridge as Transport
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.ObserverRefinementLatticeExact as Observer

data ToySoundSource : Set where
  sourceOff : ToySoundSource
  sourceOn : ToySoundSource

data ToySoundField : Set where
  transmittingOff : ToySoundField
  transmittingOn : ToySoundField
  absorbingOff : ToySoundField
  absorbingOn : ToySoundField

data ToyMicrophone : Set where
  selectedMicrophone : ToyMicrophone
  sourceMonitor : ToyMicrophone

data ToyReceived : Set where
  receiverSilent : ToyReceived
  receiverSignal : ToyReceived

-- A 'source' update retains the categorical environment.
applySource : ToySoundSource → ToySoundField → ToySoundField
applySource sourceOff transmittingOff = transmittingOff
applySource sourceOff transmittingOn = transmittingOff
applySource sourceOff absorbingOff = absorbingOff
applySource sourceOff absorbingOn = absorbingOff
applySource sourceOn transmittingOff = transmittingOn
applySource sourceOn transmittingOn = transmittingOn
applySource sourceOn absorbingOff = absorbingOn
applySource sourceOn absorbingOn = absorbingOn

-- The toy absorbing environment hides an active source from this observer.
toyMicrophoneReadout : ToyMicrophone → ToySoundField → ToyReceived
toyMicrophoneReadout selectedMicrophone transmittingOff = receiverSilent
toyMicrophoneReadout selectedMicrophone transmittingOn = receiverSignal
toyMicrophoneReadout selectedMicrophone absorbingOff = receiverSilent
toyMicrophoneReadout selectedMicrophone absorbingOn = receiverSilent
toyMicrophoneReadout sourceMonitor transmittingOff = receiverSilent
toyMicrophoneReadout sourceMonitor transmittingOn = receiverSignal
toyMicrophoneReadout sourceMonitor absorbingOff = receiverSilent
toyMicrophoneReadout sourceMonitor absorbingOn = receiverSignal

toyTransportSystem : Transport.TransportSystem
toyTransportSystem = record
  { State = ToySoundField
  ; Source = ToySoundSource
  ; Observer = ToyMicrophone
  ; Sample = ToyReceived
  ; advance = applySource
  ; observe = toyMicrophoneReadout
  }

selectedMicrophoneProjection : ToySoundField → ToyReceived
selectedMicrophoneProjection =
  toyMicrophoneReadout selectedMicrophone

-- The idealised source-side monitor reads source activity before the toy
-- environment hides it. It is an extra instrument assumption, not a free
-- consequence of the first microphone's silent reading.
sourceMonitorProjection : ToySoundField → ToyReceived
sourceMonitorProjection =
  toyMicrophoneReadout sourceMonitor

jointReceiverAndSourceMonitor :
  ToySoundField → ToyReceived × ToyReceived
jointReceiverAndSourceMonitor =
  Observer.pairObserver selectedMicrophoneProjection sourceMonitorProjection

data SourceActivity : Set where
  sourceInactive : SourceActivity
  sourceActive : SourceActivity

sourceActivity : ToySoundField → SourceActivity
sourceActivity transmittingOff = sourceInactive
sourceActivity transmittingOn = sourceActive
sourceActivity absorbingOff = sourceInactive
sourceActivity absorbingOn = sourceActive

data ToyQuery : Set where
  receiverQuestion : ToyQuery
  emitterQuestion : ToyQuery

data ToyAnswer : Set where
  receiverSilentAnswer : ToyAnswer
  receiverSignalAnswer : ToyAnswer
  emitterInactiveAnswer : ToyAnswer
  emitterActiveAnswer : ToyAnswer

readAnswer : ToyQuery → ToySoundField → ToyAnswer
readAnswer receiverQuestion transmittingOff = receiverSilentAnswer
readAnswer receiverQuestion transmittingOn = receiverSignalAnswer
readAnswer receiverQuestion absorbingOff = receiverSilentAnswer
readAnswer receiverQuestion absorbingOn = receiverSilentAnswer
readAnswer emitterQuestion transmittingOff = emitterInactiveAnswer
readAnswer emitterQuestion transmittingOn = emitterActiveAnswer
readAnswer emitterQuestion absorbingOff = emitterInactiveAnswer
readAnswer emitterQuestion absorbingOn = emitterActiveAnswer

toyQuerySemantics : Query.QuerySemantics ToySoundField ToyQuery ToyAnswer
toyQuerySemantics = Query.querySemantics readAnswer

receiverProjectionAdequateForReceiverQuestion :
  Query.AdequateFor
    selectedMicrophoneProjection toyQuerySemantics receiverQuestion
receiverProjectionAdequateForReceiverQuestion =
  Query.factorsForQuery
    {project = selectedMicrophoneProjection}
    {semantics = toyQuerySemantics}
    {query = receiverQuestion}
    (λ { receiverSilent → receiverSilentAnswer
       ; receiverSignal → receiverSignalAnswer })
    (λ { transmittingOff → refl
       ; transmittingOn → refl
       ; absorbingOff → refl
       ; absorbingOn → refl })

sourceActivityCollision :
  Query.QueryAdequacyDefect
    selectedMicrophoneProjection toyQuerySemantics emitterQuestion
sourceActivityCollision =
  Query.queryAdequacyDefect
    {project = selectedMicrophoneProjection}
    {semantics = toyQuerySemantics}
    {query = emitterQuestion}
    transmittingOff absorbingOn refl (λ ())

sameReceiverReadoutCannotRecoverEmitterActivity :
  Query.AdequateFor
    selectedMicrophoneProjection toyQuerySemantics emitterQuestion → ⊥
sameReceiverReadoutCannotRecoverEmitterActivity =
  Query.queryAdequacyDefectBlocksFactorisation sourceActivityCollision

------------------------------------------------------------------------
-- A genuinely additional observer can resolve this toy inverse ambiguity.
-- This conditional result does not establish field or material identity.
------------------------------------------------------------------------

sourceMonitorAdequateForEmitterQuestion :
  Query.AdequateFor
    sourceMonitorProjection toyQuerySemantics emitterQuestion
sourceMonitorAdequateForEmitterQuestion =
  Query.factorsForQuery
    {project = sourceMonitorProjection}
    {semantics = toyQuerySemantics}
    {query = emitterQuestion}
    (λ { receiverSilent → emitterInactiveAnswer
       ; receiverSignal → emitterActiveAnswer })
    (λ { transmittingOff → refl
       ; transmittingOn → refl
       ; absorbingOff → refl
       ; absorbingOn → refl })

sourceMonitorSeparatesSilentSourceCollision :
  sourceMonitorProjection transmittingOff
    ≡ sourceMonitorProjection absorbingOn → ⊥
sourceMonitorSeparatesSilentSourceCollision ()

-- Direct reuse of the canonical strict observer-refinement theorem:
-- the joint observer refines the original receiver, and one previously
-- colliding source/environment pair separates in the added monitor.
sourceMonitorStrictlyRefinesSelectedReceiver :
  Observer.StrictRefinement
    selectedMicrophoneProjection jointReceiverAndSourceMonitor
sourceMonitorStrictlyRefinesSelectedReceiver =
  Observer.strictPairRefinement
    selectedMicrophoneProjection
    sourceMonitorProjection
    transmittingOff absorbingOn
    refl
    sourceMonitorSeparatesSilentSourceCollision

-- This is the existing owner-specific observer equivalence, not equality
-- of fields, sources, or biological effects.
sameSampleAtSelectedObserver :
  Transport._≈[_]_ {system = toyTransportSystem}
    transmittingOff selectedMicrophone absorbingOn
sameSampleAtSelectedObserver = refl

-- Applying the same off/on source to a fixed environment can change this
-- selected receiver sample in the transmitting case. This is not a
-- universal physical transfer or any licence to infer an effect on people.
toySourceOnVsOffObservable :
  selectedMicrophoneProjection
    (applySource sourceOff transmittingOff)
  ≡ receiverSilent
toySourceOnVsOffObservable = refl

toySourceOnProducesSignalInTransmittingCase :
  selectedMicrophoneProjection
    (applySource sourceOn transmittingOff)
  ≡ receiverSignal
toySourceOnProducesSignalInTransmittingCase = refl
