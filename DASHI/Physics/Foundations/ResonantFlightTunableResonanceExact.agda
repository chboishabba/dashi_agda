module DASHI.Physics.Foundations.ResonantFlightTunableResonanceExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Structural resonance layer.  Numeric realizations may later instantiate
-- omega^2 = k / I; this module records the exact dependency and retuning
-- obligations without assuming a particular scalar field.
------------------------------------------------------------------------

record ResonanceLaw : Set₁ where
  constructor resonance-law
  field
    Inertia Stiffness Frequency : Set
    naturalFrequency : Inertia → Stiffness → Frequency

open ResonanceLaw public

record TunableResonance (R : ResonanceLaw) : Set₁ where
  constructor tunable-resonance
  field
    Control : Set
    inertia :
      Control → ResonanceLaw.Inertia R
    stiffness :
      Control → ResonanceLaw.Stiffness R
    frequency :
      Control → ResonanceLaw.Frequency R
    frequency-follows-law :
      (u : Control) →
      frequency u ≡
      ResonanceLaw.naturalFrequency R (inertia u) (stiffness u)

open TunableResonance public

record LoadedResonator : Set₁ where
  constructor loaded-resonator
  field
    Control AirState : Set
    NaturalFrequency LoadedFrequency : Set
    unloaded : Control → NaturalFrequency
    loaded : Control → AirState → LoadedFrequency

open LoadedResonator public

record ResonanceRetuning : Set₁ where
  constructor resonance-retuning
  field
    Control Frequency : Set
    baselineControl : Control
    baselineFrequency : Frequency
    tunedFrequency : Control → Frequency
    baseline-is-tuned :
      tunedFrequency baselineControl ≡ baselineFrequency

open ResonanceRetuning public

baselineRetuningIsIdentity :
  (R : ResonanceRetuning) →
  tunedFrequency R (baselineControl R) ≡ baselineFrequency R
baselineRetuningIsIdentity R =
  baseline-is-tuned R
