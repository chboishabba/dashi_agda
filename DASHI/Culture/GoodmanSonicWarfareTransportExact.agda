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
import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Core.FrozenHeldOutRepairRefinementExact as FrozenHeldOut
import DASHI.Culture.GoodmanSonicWarfareRationalInverseExact as RationalInverse

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


------------------------------------------------------------------------
-- T4: THE INVERSE PROBLEM IS ONLY PARTLY REPAIRED BY A SOURCE MONITOR.
--
-- The previous theorem established adequacy for source activity.
-- It did NOT show that the source+receiver jointly determines the medium.
-- Below, transmittingOff and absorbingOff still coincide in BOTH readings.
-- A third, independently justified environment observer separates those
-- worlds. This is an observer hierarchy, not a free physical sensor.
--
-- The finiteness and the four labels are DASHI application constructions;
-- the generic strict-refinement/separation owners remain in
-- DASHI.Core.ObserverRefinementLatticeExact.
------------------------------------------------------------------------

data ToyMedium : Set where
  toyTransmitting : ToyMedium
  toyAbsorbing : ToyMedium

toyMedium : ToySoundField → ToyMedium
toyMedium transmittingOff = toyTransmitting
toyMedium transmittingOn = toyTransmitting
toyMedium absorbingOff = toyAbsorbing
toyMedium absorbingOn = toyAbsorbing

-- Both original sensors report silence with the source off, even though
-- one toy environment transmits and the other absorbs.
sameReceiverAndSourceReadingForDifferentMedia :
  jointReceiverAndSourceMonitor transmittingOff
    ≡ jointReceiverAndSourceMonitor absorbingOff
sameReceiverAndSourceReadingForDifferentMedia = refl

differentMediaInSilentWorlds :
  toyMedium transmittingOff ≡ toyMedium absorbingOff → ⊥
differentMediaInSilentWorlds ()

jointObserverDoesNotIdentifyWholeWorld :
  Observer.Separating jointReceiverAndSourceMonitor → ⊥
jointObserverDoesNotIdentifyWholeWorld separating
  with separating transmittingOff absorbingOff
    sameReceiverAndSourceReadingForDifferentMedia
... | ()

-- This additional observer is intentionally an idealised *medium* label:
-- no sound-only algorithm or physical calibration creates it automatically.
fullToyObservation : ToySoundField →
  (ToyReceived × ToyReceived) × ToyMedium
fullToyObservation =
  Observer.pairObserver jointReceiverAndSourceMonitor toyMedium

fullObserverStrictlyRefinesJointObserver :
  Observer.StrictRefinement
    jointReceiverAndSourceMonitor fullToyObservation
fullObserverStrictlyRefinesJointObserver =
  Observer.strictPairRefinement
    jointReceiverAndSourceMonitor
    toyMedium
    transmittingOff absorbingOff
    sameReceiverAndSourceReadingForDifferentMedia
    differentMediaInSilentWorlds

-- All sixteen cases are closed; the diagonal case is reflexive and the
-- other twelve have constructor-distinct full observations.
fullObserverSeparatesToyWorlds :
  Observer.Separating fullToyObservation
fullObserverSeparatesToyWorlds transmittingOff transmittingOff _ = refl
fullObserverSeparatesToyWorlds transmittingOff transmittingOn ()
fullObserverSeparatesToyWorlds transmittingOff absorbingOff ()
fullObserverSeparatesToyWorlds transmittingOff absorbingOn ()
fullObserverSeparatesToyWorlds transmittingOn transmittingOff ()
fullObserverSeparatesToyWorlds transmittingOn transmittingOn _ = refl
fullObserverSeparatesToyWorlds transmittingOn absorbingOff ()
fullObserverSeparatesToyWorlds transmittingOn absorbingOn ()
fullObserverSeparatesToyWorlds absorbingOff transmittingOff ()
fullObserverSeparatesToyWorlds absorbingOff transmittingOn ()
fullObserverSeparatesToyWorlds absorbingOff absorbingOff _ = refl
fullObserverSeparatesToyWorlds absorbingOff absorbingOn ()
fullObserverSeparatesToyWorlds absorbingOn transmittingOff ()
fullObserverSeparatesToyWorlds absorbingOn transmittingOn ()
fullObserverSeparatesToyWorlds absorbingOn absorbingOff ()
fullObserverSeparatesToyWorlds absorbingOn absorbingOn _ = refl

-- Boundary: this conditional finite observer includes the idealised medium
-- coordinate. It does not solve generic acoustic phase retrieval, assign an
-- emitter from arbitrary real recordings, or measure a physical material.


------------------------------------------------------------------------
-- T5 / PARETO: THREE OBSERVERS ARE NOT A MINIMAL SUFFICIENT CUT.
--
-- The idealised source monitor plus the separately supplied medium label
-- already distinguishes all four finite source/environment states. The
-- selected downstream receiver adds NO further information about which of
-- these four worlds is present once the two coordinates are known.
--
-- This is relative to the fixed set of three named instruments, not a
-- universal sensor optimum, engineering cost minimum or calibration.
------------------------------------------------------------------------

sourceAndMedium : ToySoundField → ToyReceived × ToyMedium
sourceAndMedium =
  Observer.pairObserver sourceMonitorProjection toyMedium

-- A single source monitor cannot determine the medium.
sourceMonitorNotWorldSeparating :
  Observer.Separating sourceMonitorProjection → ⊥
sourceMonitorNotWorldSeparating separating
  with separating transmittingOff absorbingOff refl
... | ()

-- A single medium observer cannot determine whether its source is on.
mediumMonitorNotWorldSeparating :
  Observer.Separating toyMedium → ⊥
mediumMonitorNotWorldSeparating separating
  with separating transmittingOff transmittingOn refl
... | ()

receiverAndMedium : ToySoundField → ToyReceived × ToyMedium
receiverAndMedium =
  Observer.pairObserver selectedMicrophoneProjection toyMedium

-- Even knowing the medium, a fully absorbing receiver cannot distinguish
-- an active from an inactive source in this fixture.
receiverAndMediumNotWorldSeparating :
  Observer.Separating receiverAndMedium → ⊥
receiverAndMediumNotWorldSeparating separating
  with separating absorbingOff absorbingOn refl
... | ()

sourceAndMediumSeparatesAllFourWorlds :
  Observer.Separating sourceAndMedium
sourceAndMediumSeparatesAllFourWorlds transmittingOff transmittingOff _ = refl
sourceAndMediumSeparatesAllFourWorlds transmittingOff transmittingOn ()
sourceAndMediumSeparatesAllFourWorlds transmittingOff absorbingOff ()
sourceAndMediumSeparatesAllFourWorlds transmittingOff absorbingOn ()
sourceAndMediumSeparatesAllFourWorlds transmittingOn transmittingOff ()
sourceAndMediumSeparatesAllFourWorlds transmittingOn transmittingOn _ = refl
sourceAndMediumSeparatesAllFourWorlds transmittingOn absorbingOff ()
sourceAndMediumSeparatesAllFourWorlds transmittingOn absorbingOn ()
sourceAndMediumSeparatesAllFourWorlds absorbingOff transmittingOff ()
sourceAndMediumSeparatesAllFourWorlds absorbingOff transmittingOn ()
sourceAndMediumSeparatesAllFourWorlds absorbingOff absorbingOff _ = refl
sourceAndMediumSeparatesAllFourWorlds absorbingOff absorbingOn ()
sourceAndMediumSeparatesAllFourWorlds absorbingOn transmittingOff ()
sourceAndMediumSeparatesAllFourWorlds absorbingOn transmittingOn ()
sourceAndMediumSeparatesAllFourWorlds absorbingOn absorbingOff ()
sourceAndMediumSeparatesAllFourWorlds absorbingOn absorbingOn _ = refl

-- Recover the omitted downstream receiver reading by a finite truth
-- table once the source monitor and medium are known. This is a *toy*
-- predictive law, not a physical inverse or general attenuation equation.
recoverFullFromPareto :
  ToyReceived × ToyMedium →
  (ToyReceived × ToyReceived) × ToyMedium
recoverFullFromPareto (receiverSilent , toyTransmitting) =
  (receiverSilent , receiverSilent) , toyTransmitting
recoverFullFromPareto (receiverSignal , toyTransmitting) =
  (receiverSignal , receiverSignal) , toyTransmitting
recoverFullFromPareto (receiverSilent , toyAbsorbing) =
  (receiverSilent , receiverSilent) , toyAbsorbing
recoverFullFromPareto (receiverSignal , toyAbsorbing) =
  (receiverSilent , receiverSignal) , toyAbsorbing

fullObservationFactorsThroughParetoPair :
  (state : ToySoundField) →
  fullToyObservation state ≡ recoverFullFromPareto (sourceAndMedium state)
fullObservationFactorsThroughParetoPair transmittingOff = refl
fullObservationFactorsThroughParetoPair transmittingOn = refl
fullObservationFactorsThroughParetoPair absorbingOff = refl
fullObservationFactorsThroughParetoPair absorbingOn = refl

-- The reverse projection simply forgets the downstream receiver:
-- both observation packages have exactly the same four-world fibres.
forgetReceiverFromFull :
  (ToyReceived × ToyReceived) × ToyMedium →
  ToyReceived × ToyMedium
forgetReceiverFromFull ((receiver , source) , medium) = source , medium

paretoPairFactorsThroughFullObservation :
  (state : ToySoundField) →
  sourceAndMedium state ≡ forgetReceiverFromFull (fullToyObservation state)
paretoPairFactorsThroughFullObservation transmittingOff = refl
paretoPairFactorsThroughFullObservation transmittingOn = refl
paretoPairFactorsThroughFullObservation absorbingOff = refl
paretoPairFactorsThroughFullObservation absorbingOn = refl

-- Only *relative* minimality was shown. The medium coordinate was assumed
-- independently observable. No measured sensor, instrumentation budget,
-- physical constitutive law or new causal force is supplied.

------------------------------------------------------------------------
-- T6: ROBUST INVERSION / OUT-OF-SAMPLE AUTHORITY DOES NOT FOLLOW.
--
-- The 2x2 rational example in scripts/check_goodman_inverse_stability_finite.py
-- distinguishes invertibility from a uniform noise-amplification bound.
-- It is an executed finite regression, not an Agda proof of a general
-- real-matrix theorem. The following direct re-exports are inherited,
-- separately authored anti-promotion results, not new DASHI theorems.
------------------------------------------------------------------------

sonicFitDoesNotEstablishAdequacy :
  (Robust.fit Robust.adequateModel
    ≡ Robust.fit Robust.inadequateModel) ×
  (Robust.adequate Robust.adequateModel
    ≡ Robust.adequate Robust.inadequateModel → ⊥)
sonicFitDoesNotEstablishAdequacy = Robust.sameFitDifferentAdequacy

sonicTrainingFitDoesNotPayHeldOutValidation :
  FrozenHeldOut.TrainingFitCreatesHeldOutValidity → ⊥
sonicTrainingFitDoesNotPayHeldOutValidation =
  FrozenHeldOut.trainingFitDoesNotCreateHeldOutValidity

