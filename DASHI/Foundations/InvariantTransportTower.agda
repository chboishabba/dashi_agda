module DASHI.Foundations.InvariantTransportTower where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (suc)

import DASHI.Foundations.InvolutiveTernaryRenormalisation as R

record TransportedInvariantTower
  (T : R.InvolutiveScaleTower)
  (D : R.LiftedInvolutiveDynamics T) : Set₁ where
  field
    invariantTower : R.InvariantTower T D

    quotientValue : ∀ j →
      R.Value invariantTower j →
      R.Value invariantTower (suc j)

    read-coarse-commutes : ∀ j s →
      R.read invariantTower (suc j) (R.coarse T j s) ≡
      quotientValue j (R.read invariantTower j s)

open TransportedInvariantTower public

transportedTransitionInvariant : ∀
  {T D}
  (J : TransportedInvariantTower T D)
  j s u →
  quotientValue J j
    (R.read (invariantTower J) j (R.step D j s u)) ≡
  quotientValue J j
    (R.read (invariantTower J) j s)
transportedTransitionInvariant J j s u
  rewrite R.transition-invariant (invariantTower J) j s u = refl
