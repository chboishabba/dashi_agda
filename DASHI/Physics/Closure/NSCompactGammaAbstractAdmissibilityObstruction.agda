module DASHI.Physics.Closure.NSCompactGammaAbstractAdmissibilityObstruction where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
import Data.Nat as ℕ

open import DASHI.Physics.Closure.NSCompactGammaAdmissiblePreservation

------------------------------------------------------------------------
-- A concrete countermodel to the implication
--
--   CompactGammaAdmissible -> five-halves exponential shell envelope
--
-- at the abstract record level.
--
-- The admissibility record constrains gamma, packet energy, one undifferentiated
-- state-size scalar and the total off-packet ratio.  It does not mention a
-- shell-by-shell weighted profile.  Therefore no theorem may derive the desired
-- pointwise shell envelope from `CompactGammaAdmissible` alone.  The Fourier
-- dynamics, a distance-weighted size norm, or another explicit analytic input is
-- logically necessary.
------------------------------------------------------------------------

data NeverLess (a b : Nat) : Set where

nat≤-refl : ∀ {n} → n ℕ.≤ n
nat≤-refl {zero} = ℕ.z≤n
nat≤-refl {suc n} = ℕ.s≤s nat≤-refl

nat≤-trans : ∀ {a b c} → a ℕ.≤ b → b ℕ.≤ c → a ℕ.≤ c
nat≤-trans ℕ.z≤n q = ℕ.z≤n
nat≤-trans (ℕ.s≤s p) (ℕ.s≤s q) = ℕ.s≤s (nat≤-trans p q)

natOrderedScalar : OrderedScalar lzero
natOrderedScalar = record
  { Scalar = Nat
  ; _≤_ = ℕ._≤_
  ; _<_ = NeverLess
  ; ≤-refl = nat≤-refl
  ; ≤-trans = nat≤-trans
  ; <-irrefl-from-≤ = λ ()
  }

abstractSystem : CompactGammaSystem natOrderedScalar ⊤ Nat
abstractSystem = record
  { gamma = λ _ _ → suc zero
  ; packetEnergy = λ _ _ → suc zero
  ; stateSize = λ _ → zero
  ; offPacketRatio = λ _ _ → zero
  ; Reality = λ _ → ⊤
  ; DivergenceFree = λ _ → ⊤
  }

abstractThresholds : CompactGammaThresholds natOrderedScalar
abstractThresholds = record
  { gammaFloor = suc zero
  ; energyFloor = suc zero
  ; sizeCeiling = zero
  ; offPacketCeiling = zero
  }

abstractAdmissible :
  CompactGammaAdmissible
    abstractSystem abstractThresholds zero tt
abstractAdmissible = record
  { gammaAboveFloor = ℕ.s≤s ℕ.z≤n
  ; packetEnergyAboveFloor = ℕ.s≤s ℕ.z≤n
  ; sizeBelowCeiling = ℕ.z≤n
  ; offPacketRatioBelowCeiling = ℕ.z≤n
  ; realityPreserved = tt
  ; divergenceFreePreserved = tt
  }

abstractWeightedFiveHalvesShell : Nat → Nat
abstractWeightedFiveHalvesShell zero = zero
abstractWeightedFiveHalvesShell (suc _) = suc zero

abstractDecayCoefficient : Nat → Nat
abstractDecayCoefficient _ = zero

abstractEnvelope : Nat
abstractEnvelope = zero

oneNotBelowZero : ¬ (suc zero ℕ.≤ zero)
oneNotBelowZero ()

record AbstractAdmissibilityShellDecayObstruction : Set where
  field
    admissible :
      CompactGammaAdmissible
        abstractSystem abstractThresholds zero tt
    violatingShell : Nat
    shellDecayFails :
      ¬ (abstractWeightedFiveHalvesShell violatingShell ℕ.≤
          (abstractDecayCoefficient violatingShell ℕ.+ abstractEnvelope))

open AbstractAdmissibilityShellDecayObstruction public

abstractCompactGammaAdmissibilityDoesNotForceFiveHalves :
  AbstractAdmissibilityShellDecayObstruction
abstractCompactGammaAdmissibilityDoesNotForceFiveHalves = record
  { admissible = abstractAdmissible
  ; violatingShell = suc zero
  ; shellDecayFails = oneNotBelowZero
  }
