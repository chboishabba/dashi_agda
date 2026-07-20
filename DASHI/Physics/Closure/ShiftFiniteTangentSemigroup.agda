module DASHI.Physics.Closure.ShiftFiniteTangentSemigroup where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- Exact finite tangent surrogate around the held fixed point.
--
-- The carrier records the two transient displacement classes and the zero
-- perturbation at held.  It is not a vector space, normed tangent bundle, or
-- Frechet tangent object.  The induced step is the exact finite shift step.

data ShiftFinitePerturbation : Set where
  startPerturbation : ShiftFinitePerturbation
  nextPerturbation : ShiftFinitePerturbation
  zeroPerturbation : ShiftFinitePerturbation

perturbationState :
  ShiftFinitePerturbation →
  SPTI.ShiftPressurePoint
perturbationState startPerturbation = SPTI.shiftStartPoint
perturbationState nextPerturbation = SPTI.shiftNextPoint
perturbationState zeroPerturbation = SPTI.shiftHeldExitPoint

finiteDerivativeStep :
  ShiftFinitePerturbation →
  ShiftFinitePerturbation
finiteDerivativeStep startPerturbation = nextPerturbation
finiteDerivativeStep nextPerturbation = zeroPerturbation
finiteDerivativeStep zeroPerturbation = zeroPerturbation

finiteDerivativeStateCoherence :
  (p : ShiftFinitePerturbation) →
  perturbationState (finiteDerivativeStep p)
    ≡
  DDSI.shiftPressureAdvance (perturbationState p)
finiteDerivativeStateCoherence startPerturbation = refl
finiteDerivativeStateCoherence nextPerturbation = refl
finiteDerivativeStateCoherence zeroPerturbation = refl

iterate :
  {A : Set} →
  Nat →
  (A → A) →
  A →
  A
iterate zero f x = x
iterate (suc n) f x = iterate n f (f x)

iterate-plus :
  {A : Set} →
  (m n : Nat) →
  (f : A → A) →
  (x : A) →
  iterate (m + n) f x ≡ iterate n f (iterate m f x)
iterate-plus zero n f x = refl
iterate-plus (suc m) n f x = iterate-plus m n f (f x)

finiteTimeAction :
  Nat →
  ShiftFinitePerturbation →
  ShiftFinitePerturbation
finiteTimeAction n = iterate n finiteDerivativeStep

finiteTimeZero :
  (p : ShiftFinitePerturbation) →
  finiteTimeAction zero p ≡ p
finiteTimeZero p = refl

finiteTimeComposition :
  (m n : Nat) →
  (p : ShiftFinitePerturbation) →
  finiteTimeAction (m + n) p
    ≡
  finiteTimeAction n (finiteTimeAction m p)
finiteTimeComposition m n p =
  iterate-plus m n finiteDerivativeStep p

finiteZeroStable :
  finiteDerivativeStep zeroPerturbation ≡ zeroPerturbation
finiteZeroStable = refl

finiteAbsorbsFromTwo :
  (n : Nat) →
  (p : ShiftFinitePerturbation) →
  finiteTimeAction (suc (suc n)) p ≡ zeroPerturbation
finiteAbsorbsFromTwo zero startPerturbation = refl
finiteAbsorbsFromTwo zero nextPerturbation = refl
finiteAbsorbsFromTwo zero zeroPerturbation = refl
finiteAbsorbsFromTwo (suc n) p
  rewrite finiteAbsorbsFromTwo n (finiteDerivativeStep p)
  = refl

record ShiftFiniteTangentSemigroup : Setω where
  field
    Perturbation : Set
    zeroPoint : Perturbation
    stateOf : Perturbation → SPTI.ShiftPressurePoint
    derivativeStep : Perturbation → Perturbation
    timeAction : Nat → Perturbation → Perturbation

    stateCoherence :
      (p : Perturbation) →
      stateOf (derivativeStep p)
        ≡
      DDSI.shiftPressureAdvance (stateOf p)

    zeroTime :
      (p : Perturbation) →
      timeAction zero p ≡ p

    composition :
      (m n : Nat) →
      (p : Perturbation) →
      timeAction (m + n) p
        ≡
      timeAction n (timeAction m p)

    zeroStable : derivativeStep zeroPoint ≡ zeroPoint

    absorbedFromTwo :
      (n : Nat) →
      (p : Perturbation) →
      timeAction (suc (suc n)) p ≡ zeroPoint

    nonClaimBoundary : List String

open ShiftFiniteTangentSemigroup public

canonicalShiftFiniteTangentSemigroup :
  ShiftFiniteTangentSemigroup
canonicalShiftFiniteTangentSemigroup =
  record
    { Perturbation = ShiftFinitePerturbation
    ; zeroPoint = zeroPerturbation
    ; stateOf = perturbationState
    ; derivativeStep = finiteDerivativeStep
    ; timeAction = finiteTimeAction
    ; stateCoherence = finiteDerivativeStateCoherence
    ; zeroTime = finiteTimeZero
    ; composition = finiteTimeComposition
    ; zeroStable = finiteZeroStable
    ; absorbedFromTwo = finiteAbsorbsFromTwo
    ; nonClaimBoundary =
        "ShiftFiniteTangentSemigroup is an exact finite pointed perturbation carrier"
        ∷ "finiteDerivativeStep is the exact induced shift step, not a Frechet derivative"
        ∷ "finiteTimeComposition is a Nat-indexed iteration semigroup law"
        ∷ "No additive tangent space, scalar action, norm, generator, or continuous-time semigroup is claimed"
        ∷ []
    }
