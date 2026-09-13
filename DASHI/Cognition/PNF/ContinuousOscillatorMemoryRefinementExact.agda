module DASHI.Cognition.PNF.ContinuousOscillatorMemoryRefinementExact where

open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- Structural continuous-oscillator refinement carrier.
--
-- Intended numerical realisation (not implemented or promoted here):
--
--   psi_i(t) = A_i exp(i(omega_i t + phi_i))
--   Psi(t)   = sum_i w_i psi_i(t)
--
-- The Agda carrier below deliberately records only the types and observation
-- boundaries required by such a producer.  In particular, ContinuousPhase is
-- not definitionally DASHI.Cognition.PhaseEnrichedTrit.Phase3, and HiddenField
-- is not claimed to be a Hilbert space or a complex vector space.
------------------------------------------------------------------------

record OscillatorSchema : Set₁ where
  field
    Mode : Set
    Amplitude : Set
    Frequency : Set
    ContinuousPhase : Set
    Coupling : Set
    HiddenField : Set

    assembleMode :
      Mode → Amplitude → Frequency → ContinuousPhase → Coupling → HiddenField

open OscillatorSchema public

record HiddenOscillatorState (O : OscillatorSchema) : Set where
  constructor hiddenOscillatorState
  field
    hiddenField : HiddenField O

open HiddenOscillatorState public

------------------------------------------------------------------------
-- Gauge / observational quotient seam.
--
-- A future numerical realisation may prove global-phase, time-origin, or
-- amplitude/weight rescaling symmetries.  This owner does not assume those
-- symmetries.  It only provides the relation and observer-soundness shape
-- needed once a concrete realisation supplies them.
------------------------------------------------------------------------

record HiddenObservationQuotient
  (Hidden Public : Set) : Set₁ where
  field
    EquivalentHiddenState : Hidden → Hidden → Set
    observe : Hidden → Public
    observerSound :
      ∀ x y → EquivalentHiddenState x y → observe x ≡ observe y

open HiddenObservationQuotient public
