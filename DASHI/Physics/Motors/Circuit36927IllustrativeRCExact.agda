module DASHI.Physics.Motors.Circuit36927IllustrativeRCExact where

------------------------------------------------------------------------
-- DASHI-authored simple RC demonstration; no connection to a claimed
-- Resonate369 circuit and no manufacturer/CAD source ingestion.
-- The values are inputs to a reusable graph, not measured behavior.
-- Graph traversal is not a proof of current continuity through R/C.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import DASHI.Physics.Motors.Circuit36927ComponentGraphExact as C

open C using
  (Part; part; Wire; wire; Circuit; circuit; Pin; pin;
   Endpoint; atPin; NominalValue; milliohms; picofarads;
   millivolts; Dimension; resistance; capacitance; voltage;
   resistor; capacitor; voltageSource; valueDimension)

illustrativeSupply : Part
illustrativeSupply =
  part 0 voltageSource "V1" (millivolts 12000) 2

illustrativeResistor : Part
illustrativeResistor =
  part 1 resistor "R1" (milliohms 1000000) 2

illustrativeCapacitor : Part
illustrativeCapacitor =
  part 2 capacitor "C1" (picofarads 3300000) 2

supplyDimension :
  valueDimension (Part.nominal illustrativeSupply) ≡ voltage
supplyDimension = refl

resistorDimension :
  valueDimension (Part.nominal illustrativeResistor) ≡ resistance
resistorDimension = refl

capacitorDimension :
  valueDimension (Part.nominal illustrativeCapacitor) ≡ capacitance
capacitorDimension = refl

examplePart : Nat → Part
examplePart zero = illustrativeSupply
examplePart (suc zero) = illustrativeResistor
examplePart (suc (suc _)) = illustrativeCapacitor

exampleWire : Nat → Wire
exampleWire zero =
  wire (atPin (pin 0 0)) (atPin (pin 1 0))
exampleWire (suc zero) =
  wire (atPin (pin 1 1)) (atPin (pin 2 0))
exampleWire (suc (suc _)) =
  wire (atPin (pin 2 1)) (atPin (pin 0 1))

illustrativeRC : Circuit
illustrativeRC =
  circuit examplePart 3 exampleWire 3 "DASHI illustrative RC v1"

-- The graph carries real user-supplied R/C units and terminals,
-- but does not pretend that a resistor or capacitor is a direct
-- wire, or that a voltage transient has been solved.
