module DASHI.Foundations.DefectValuedCommutation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Nat.Base using (_≤_; z≤n)

import DASHI.Foundations.InvolutiveTernaryRenormalisation as R

------------------------------------------------------------------------
-- Approximate commuting squares.
--
-- Exact commutation remains available in LiftedInvolutiveDynamics.  This
-- record permits an application to measure the mismatch between coarse-after-
-- step and step-after-coarse and to prove a scale-dependent bound.

record DefectValuedCommutation
  (T : R.InvolutiveScaleTower)
  (D : R.LiftedInvolutiveDynamics T) : Set₁ where
  field
    distance : ∀ j → R.Carrier T j → R.Carrier T j → Nat
    distance-self : ∀ j x → distance j x x ≡ zero

    tolerance : Nat → Nat

    defect : ∀ j (s : R.Carrier T j) (u : R.Control D j) → Nat
    defect-is-distance : ∀ j s u →
      defect j s u ≡
      distance (Agda.Builtin.Nat.suc j)
        (R.coarse T j (R.step D j s u))
        (R.step D (Agda.Builtin.Nat.suc j)
          (R.coarse T j s)
          (R.liftControl D j u))

    defect-bounded : ∀ j s u → defect j s u ≤ tolerance j

open DefectValuedCommutation public

------------------------------------------------------------------------
-- Any exactly commuting lifted dynamics has zero defect for every reflexive
-- Nat-valued distance.

exactDefect : ∀
  (T : R.InvolutiveScaleTower)
  (D : R.LiftedInvolutiveDynamics T)
  (distance : ∀ j → R.Carrier T j → R.Carrier T j → Nat)
  (distance-self : ∀ j x → distance j x x ≡ zero)
  (j : Nat)
  (s : R.Carrier T j)
  (u : R.Control D j) → Nat
exactDefect T D distance distance-self j s u =
  distance (Agda.Builtin.Nat.suc j)
    (R.coarse T j (R.step D j s u))
    (R.step D (Agda.Builtin.Nat.suc j)
      (R.coarse T j s)
      (R.liftControl D j u))

exactDefect-zero : ∀ T D distance distance-self j s u →
  exactDefect T D distance distance-self j s u ≡ zero
exactDefect-zero T D distance distance-self j s u
  rewrite R.coarse-step-commutes D j s u =
  distance-self (Agda.Builtin.Nat.suc j)
    (R.step D (Agda.Builtin.Nat.suc j)
      (R.coarse T j s)
      (R.liftControl D j u))

exactDefect-boundedByZero : ∀ T D distance distance-self j s u →
  exactDefect T D distance distance-self j s u ≤ zero
exactDefect-boundedByZero T D distance distance-self j s u
  rewrite exactDefect-zero T D distance distance-self j s u = z≤n
