module DASHI.Physics.Measurement.BioEMNonidentifiabilityExact where

-- A constructive finite counterexample to unrestricted current-source
-- inversion from one magnetic projection. An observation map can be
-- non-injective even when it is deterministic, noiseless and calibrated.
-- This is a mathematical witness, not a model of a particular human heart.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

data Source : Set where
  sourceA sourceB : Source

data Field : Set where
  sameField : Field

data Readout : Set where
  sameReadout : Readout

forward : Source → Field
forward sourceA = sameField
forward sourceB = sameField

sensor : Field → Readout
sensor sameField = sameReadout

observation : Source → Readout
observation x = sensor (forward x)

observationsAgree :
  observation sourceA ≡ observation sourceB
observationsAgree = refl

sourceAneqB : sourceA ≡ sourceB → ⊥
sourceAneqB ()

-- No perfect reconstruction map can recover both different sources from
-- their identical observation. This is a constructive no-go for this model.
noUniversalExactDecoder :
  (decode : Readout → Source) →
  (decode (observation sourceA) ≡ sourceA) →
  (decode (observation sourceB) ≡ sourceB) →
  ⊥
noUniversalExactDecoder decode recoverA recoverB =
  sourceAneqB
    (trans (sym recoverA) recoverB)
  where
    open import Relation.Binary.PropositionalEquality using (trans; sym)
