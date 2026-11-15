module DASHI.Physics.Motors.FilsingerZVSShunt36927AdapterExact where

-- Uses the canonical component graph from #1482. This is a source-
-- qualified candidate representation of the NEW reel's 1 MOhm shunts,
-- not evidence that the red wrapped objects have been electrically probed.
-- No imported electrical oscillator, physical resonance or power theorem.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927ComponentGraphExact as G
import DASHI.Physics.Motors.FilsingerLydenCircuit36927AdapterExact as Original

-- Resistive values in the existing owner are MILLIohms.
-- 1 MOhm = 1,000,000,000 milliohms.
whiteShuntAId whiteShuntBId : Nat
whiteShuntAId = 5
whiteShuntBId = 6

whiteShuntA : G.Part
whiteShuntA = G.part whiteShuntAId G.resistor "White C shunt A: 1 MOhm narrated" (G.milliohms 1000000000) 2

whiteShuntB : G.Part
whiteShuntB = G.part whiteShuntBId G.resistor "White C shunt B: 1 MOhm narrated" (G.milliohms 1000000000) 2

-- The reel describes a resistor across *each* capacitor; which
-- exact physical capacitor terminal/bridge branch the speaker points at
-- is not proved from the photographs. These 2-pin parts are candidates.
-- A resistance declared as a component does not turn into a wire.

record ShuntConnectionAdmission : Set₁ where
  field
    actualCapacitorPositivePin : G.Endpoint
    actualCapacitorNegativePin : G.Endpoint
    actualResistorFirstPin : G.Endpoint
    actualResistorSecondPin : G.Endpoint
    observedRevision : String
    physicalTrace : Set
    tracesBothEnds : physicalTrace

-- The earlier narrated hot->Earth-negative direction remains owned
-- by Original; no missing return path or additional electrode is invented.
preservedWhiteHot : G.Endpoint
preservedWhiteHot = Original.hot

preservedNarratedEarth : G.Endpoint
preservedNarratedEarth = Original.earthNegative

-- 1 MOhm shunt loading, self-oscillating ZVS and observed Earth energy
-- are distinct obligations. Only the physical source can inhabit these.
record ElectricalShuntValidation : Set₁ where
  field
    ActualBridgeTopology : Set
    MeasuredShuntResistance : Set
    ActualElectricalOscillatorFrequency : Set
    SignedDynamicTerminalVoltage : Set
    ActualSourcePower : Set
    bridge : ActualBridgeTopology
    resistance : MeasuredShuntResistance
    frequency : ActualElectricalOscillatorFrequency
    signedVoltage : SignedDynamicTerminalVoltage
    sourcePower : ActualSourcePower
