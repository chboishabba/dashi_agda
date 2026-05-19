module DASHI.Arithmetic.VpTrue where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Relation.Binary.PropositionalEquality using (trans; sym)

open import DASHI.Arithmetic.VpDepth using
  ( vp-depth
  ; vp-depth-stable-step
  ; vp-depth-stable-next
  )

------------------------------------------------------------------------
-- Public valuation layer.
--
-- `vp-depth` remains the executable core. This module exposes the intended
-- fuel-free interface by choosing `n` itself as the public evaluation bound.
-- The adequacy proof that this agrees with all larger fuels is isolated here
-- so downstream arithmetic modules do not have to mention fuel once that
-- theorem is discharged.

vp-true : Nat → Nat → Nat
vp-true p n = vp-depth n p n

vp-true-self :
  ∀ p n →
  vp-depth n p n ≡ vp-true p n
vp-true-self _ _ = refl

------------------------------------------------------------------------
-- Adequacy surfaces.
--
-- These are the remaining valuation obligations needed to remove fuel from
-- the theorem-facing bridge. They are intentionally isolated here so the
-- currently constructive `vp-depth` path can stay in use until adequacy is
-- proved instead of being replaced by a weaker postulated bridge theorem.

postulate
  vp-depth-adequate :
    ∀ p n →
    vp-depth n p n ≡ vp-depth (suc n) p n

transport-plateau :
  ∀ fuel p n extra →
  vp-depth fuel p n ≡ vp-depth (suc fuel) p n →
  vp-depth (fuel + extra) p n ≡ vp-depth (suc (fuel + extra)) p n
transport-plateau fuel p n zero plateau
  rewrite +-identityʳ fuel
  = plateau
transport-plateau fuel p n (suc extra) plateau
  rewrite +-suc fuel extra =
  vp-depth-stable-step
    (fuel + extra)
    p
    n
    (transport-plateau fuel p n extra plateau)

plateau-iter :
  ∀ fuel p n extra →
  vp-depth fuel p n ≡ vp-depth (suc fuel) p n →
  vp-depth fuel p n ≡ vp-depth (fuel + extra) p n
plateau-iter fuel p n zero plateau rewrite +-identityʳ fuel = refl
plateau-iter fuel p n (suc extra) plateau
  rewrite +-suc fuel extra =
    trans
      (plateau-iter fuel p n extra plateau)
      (transport-plateau fuel p n extra plateau)

vp-true-stable :
  ∀ p n extra →
  vp-depth (n + extra) p n ≡ vp-true p n
vp-true-stable p n extra =
  sym (plateau-iter n p n extra (vp-depth-adequate p n))
