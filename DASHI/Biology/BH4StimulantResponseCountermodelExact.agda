module DASHI.Biology.BH4StimulantResponseCountermodelExact where

-- Synthetic finite observation obstruction; no clinical or kinetic claim.
-- Reuses existing catalytic capacity, not irreversible cofactor consumption.
open import DASHI.Core.Prelude
import DASHI.Biology.BH4CatalyticTurnoverFutureCountermodelExact as C

record Window : Set where
  constructor window
  field
    capacity : C.CatalyticCapacityScenario
    synthesis unusedCapacity initialReserve basalRelease extraRelease finalReserve : Nat
    capacityBound : synthesis + unusedCapacity ≡ C.selectedTurnoverCapacity capacity
    reserveBalance : initialReserve + synthesis ≡ basalRelease + extraRelease + finalReserve

open Window public

record Observation : Set where
  constructor observation
  field
    baselineScaled methylphenidateScaled amphetamineScaled : Nat

-- Fixed common toy clearance 2, 1, 1; all rational observations scaled by 2.
-- The balance accounts for the maximum-release window, not a drug sequence.
observe : Window → Observation
observe x = observation (basalRelease x) (2 * basalRelease x)
  (2 * (basalRelease x + extraRelease x))

pool : Window → Nat
pool x = C.availableCofactorMolecules (capacity x)

lowPool highPool unusedTurnover : Window
lowPool = window C.slowCycle 1 0 3 1 1 2 refl refl
highPool = window (C.catalytic-capacity-scenario 2 1 2 refl) 2 0 2 1 1 2 refl refl
unusedTurnover = window (C.catalytic-capacity-scenario 2 2 4 refl) 1 3 3 1 1 2 refl refl

sameObservation : observe lowPool ≡ observe highPool
sameObservation = refl

sameUnusedObservation : observe lowPool ≡ observe unusedTurnover
sameUnusedObservation = refl

differentPool : pool lowPool ≡ pool highPool → ⊥
differentPool ()

differentSynthesis : synthesis lowPool ≡ synthesis highPool → ⊥
differentSynthesis ()

observationDoesNotIdentify : (target : Window → Nat)
  (a b : Window) → observe a ≡ observe b →
  (target a ≡ target b → ⊥) →
  (predict : Observation → Nat) →
  ((x : Window) → target x ≡ predict (observe x)) → ⊥
observationDoesNotIdentify target a b same different predict factors =
  different (trans (factors a) (trans (cong predict same) (sym (factors b))))

stimulantObservationDoesNotIdentifyPool :
  (predict : Observation → Nat) →
  ((x : Window) → pool x ≡ predict (observe x)) → ⊥
stimulantObservationDoesNotIdentifyPool =
  observationDoesNotIdentify pool lowPool highPool sameObservation differentPool

stimulantObservationDoesNotIdentifySynthesis :
  (predict : Observation → Nat) →
  ((x : Window) → synthesis x ≡ predict (observe x)) → ⊥
stimulantObservationDoesNotIdentifySynthesis =
  observationDoesNotIdentify synthesis lowPool highPool sameObservation differentSynthesis

-- Identical synthesis and response are also compatible with different pool sizes.
sameSynthesisDifferentPool : pool lowPool ≡ pool unusedTurnover → ⊥
sameSynthesisDifferentPool ()

sameSynthesisAcrossPools : synthesis lowPool ≡ synthesis unusedTurnover
sameSynthesisAcrossPools = refl
