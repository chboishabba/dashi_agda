module DASHI.Physics.Closure.NSTriadKNExactFiniteModeTriadSurface where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Setω)
open import Data.Fin using (Fin)

import DASHI.Physics.Closure.NSTriadKNExactAlgebraicRetainedTriadFiber as Exact

------------------------------------------------------------------------
-- Canonical finite carriers.
--
-- The exact K_N definition is finite at every shell cutoff.  This helper
-- makes that finiteness constructive by using Fin n as the carrier itself;
-- the shell-specific mode and triad data remain explicit inputs.
------------------------------------------------------------------------

finCarrier : (n : Nat) → Exact.FiniteCarrier
finCarrier n =
  Exact.mkFiniteCarrier
    (Fin n)
    n
    (λ i → i)
    (λ x → x)
    (λ _ → refl)
    (λ _ → refl)

record FiniteModeTriadData
    (S : Exact.ExactScalarOperations) : Setω where
  constructor mkFiniteModeTriadData
  field
    modeCount : Nat
    triadCount : Nat

    triadData :
      Fin triadCount →
      Exact.TriadData
        (Fin modeCount)
        (Exact.ExactScalarOperations.Carrier S)

    triadCoherenceBound :
      (τ : Fin triadCount) →
      Exact.ExactScalarOperations.WithinMinusOneOne S
        (Exact.TriadData.gamma (triadData τ))

open FiniteModeTriadData public

finiteTriadModeSurfaceFromData :
  (S : Exact.ExactScalarOperations) →
  (d : FiniteModeTriadData S) →
  Exact.FiniteTriadModeSurface S
finiteTriadModeSurfaceFromData S d =
  Exact.mkFiniteTriadModeSurface
    (finCarrier (FiniteModeTriadData.modeCount d))
    (finCarrier (FiniteModeTriadData.triadCount d))
    (FiniteModeTriadData.triadData d)
    (FiniteModeTriadData.triadCoherenceBound d)

------------------------------------------------------------------------
-- Admissible amplitude profiles on the finite surface.
------------------------------------------------------------------------

record FiniteAmplitudeProfileData
    {S : Exact.ExactScalarOperations}
    (d : FiniteModeTriadData S) : Setω where
  constructor mkFiniteAmplitudeProfileData
  field
    probability :
      Fin (FiniteModeTriadData.modeCount d) →
      Exact.ExactScalarOperations.Carrier S

    amplitude :
      Fin (FiniteModeTriadData.modeCount d) →
      Exact.ExactScalarOperations.Carrier S

    amplitudeFormula :
      (m : Fin (FiniteModeTriadData.modeCount d)) →
      amplitude m ≡
      Exact.ExactScalarOperations.sqrt S
        (Exact.ExactScalarOperations.maxZero S (probability m))

    amplitudeNonnegative :
      (m : Fin (FiniteModeTriadData.modeCount d)) →
      Exact.ExactScalarOperations.Nonnegative S (amplitude m)

open FiniteAmplitudeProfileData public

admissibleAmplitudeProfileFromFiniteData :
  (S : Exact.ExactScalarOperations) →
  (d : FiniteModeTriadData S) →
  (profile : FiniteAmplitudeProfileData d) →
  Exact.AdmissibleAmplitudeProfile
    (finiteTriadModeSurfaceFromData S d)
admissibleAmplitudeProfileFromFiniteData S d profile =
  Exact.mkAdmissibleAmplitudeProfile
    (FiniteAmplitudeProfileData.probability profile)
    (FiniteAmplitudeProfileData.amplitude profile)
    (FiniteAmplitudeProfileData.amplitudeFormula profile)
    (FiniteAmplitudeProfileData.amplitudeNonnegative profile)

------------------------------------------------------------------------
-- Definitional transport back to the exact triad data.
------------------------------------------------------------------------

finiteSurfaceTriadDataAgrees :
  (S : Exact.ExactScalarOperations) →
  (d : FiniteModeTriadData S) →
  (τ : Fin (FiniteModeTriadData.triadCount d)) →
  Exact.FiniteTriadModeSurface.triadData
    (finiteTriadModeSurfaceFromData S d)
    τ
  ≡ FiniteModeTriadData.triadData d τ
finiteSurfaceTriadDataAgrees S d _ = refl
