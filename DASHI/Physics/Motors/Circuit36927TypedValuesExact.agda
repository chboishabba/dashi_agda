module DASHI.Physics.Motors.Circuit36927TypedValuesExact where

------------------------------------------------------------------------
-- A physically meaningful component-value type: an R cannot be given
-- a voltage, a C cannot be given an inductance and so on. Values here
-- are symbolic nominal inputs and not measurements of any device.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927ComponentGraphExact as Graph

open Graph using
  (ComponentKind; resistor; capacitor; inductor; voltageSource;
   currentSource; NominalValue; milliohms; picofarads; nanohenries;
   millivolts; microamps; unavailable; Part; part)

data ValueFor : ComponentKind → Set where
  ohmic : Nat → ValueFor resistor
  capacitive : Nat → ValueFor capacitor
  inductive : Nat → ValueFor inductor
  voltageDriven : Nat → ValueFor voltageSource
  currentDriven : Nat → ValueFor currentSource
  unspecified : (kind : ComponentKind) → ValueFor kind

eraseTypedValue : ∀ {k} → ValueFor k → NominalValue
eraseTypedValue (ohmic r) = milliohms r
eraseTypedValue (capacitive c) = picofarads c
eraseTypedValue (inductive l) = nanohenries l
eraseTypedValue (voltageDriven v) = millivolts v
eraseTypedValue (currentDriven i) = microamps i
eraseTypedValue (unspecified k) = unavailable

-- A Part retains the kind and type-indexed parameter together.
record TypedPart : Set where
  constructor typedPart
  field
    identifier : Nat
    kind : ComponentKind
    label : String
    nominal : ValueFor kind
    pins : Nat

-- A type-correct value can be erased into the previously existing
-- generic component graph without changing its kind.
toGenericPart : TypedPart → Part
toGenericPart t =
  part (TypedPart.identifier t)
       (TypedPart.kind t)
       (TypedPart.label t)
       (eraseTypedValue (TypedPart.nominal t))
       (TypedPart.pins t)

sampleResistor : TypedPart
sampleResistor =
  typedPart 1 resistor "R1" (ohmic 1000000) 2

sampleResistorErases :
  Part.nominal (toGenericPart sampleResistor) ≡
  milliohms 1000000
sampleResistorErases = refl

-- These types reject a construction such as:
-- typedPart 1 resistor "R1" (voltageDriven 12000) 2
-- by ordinary dependent type checking, not a runtime validator.
