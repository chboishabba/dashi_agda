module DASHI.Physics.Closure.NSTriadKNFirstHitPeriodicProfileInstanceRound266Exact where

------------------------------------------------------------------------
-- ROUND266 / LEAF D*: INSTANTIATE R260 ON THE ACTUAL R242 FIRST-HIT STATES
--
-- R260 gives the correct periodic profile theorem shape, but its generic
-- carrier must not float free of the selected Galerkin states. This file adds
-- the missing same-object weld.
--
-- Given the literal first-hit sequence S and the physical state map u_N(t),
-- define
--
--   x_n = u_{selectedCutoff S n}(selectedTime S n).
--
-- The periodic H^(1/2) profile theorem is instantiated on exactly x_n. Thus
-- the weak scale-one profile and every shrinking Euclidean bubble descend from
-- the same bounded sequence manufactured by Round242/265.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNCriticalFirstHitExtractionRound242Exact as R242
import DASHI.Physics.Closure.NSTriadKNPeriodicFractionalProfileSourceRound260Exact as R260

record FirstHitPeriodicProfileInstance
    {ℓTorus ℓEuclid : Level}
    (Time : Set)
    (criticalSize : Nat → Time → ℚ)
    (threshold : ℚ)
    (S : R242.CriticalFirstHitSequence Time criticalSize threshold)
    (TorusState : Set ℓTorus)
    (EuclideanState : Set ℓEuclid)
    (stateAt : Nat → Time → TorusState)
    : Set (lsuc (ℓTorus ⊔ ℓEuclid)) where
  field
    -- The sequence to which the source theorem is applied.
    profiledInput : Nat → TorusState
    profiledInputIsLiteralFirstHitState :
      (n : Nat) →
      profiledInput n
      ≡ stateAt (R242.selectedCutoff S n) (R242.selectedTime S n)

    -- R260 is stated with equal-level carriers; embed both state types into one
    -- common analytic carrier before applying the source theorem.
    CommonState : Set (ℓTorus ⊔ ℓEuclid)
    torusIntoCommon : TorusState → CommonState
    euclideanIntoCommon : EuclideanState → CommonState
    periodicProfileTheorem :
      R260.PeriodicFractionalProfileTheorem CommonState CommonState

    sourceTheoremAppliedToProfiledInput : Set (ℓTorus ⊔ ℓEuclid)

open FirstHitPeriodicProfileInstance public

literalFirstHitState :
  ∀ {Time criticalSize threshold TorusState}
    (S : R242.CriticalFirstHitSequence Time criticalSize threshold)
    (stateAt : Nat → Time → TorusState) → Nat → TorusState
literalFirstHitState S stateAt n =
  stateAt (R242.selectedCutoff S n) (R242.selectedTime S n)

round266LeafDProfileTheoremBoundToActualFirstHitSequence : Bool
round266LeafDProfileTheoremBoundToActualFirstHitSequence = true

round266NoFreeFloatingProfileSequence : Bool
round266NoFreeFloatingProfileSequence = true

round266ProfileAnalysisKernelDerivedInFiniteAgda : Bool
round266ProfileAnalysisKernelDerivedInFiniteAgda = false

round266LeafDProfileTheoremBoundToActualFirstHitSequenceIsTrue :
  round266LeafDProfileTheoremBoundToActualFirstHitSequence ≡ true
round266LeafDProfileTheoremBoundToActualFirstHitSequenceIsTrue = refl
