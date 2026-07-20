{-# OPTIONS --safe #-}
module DASHI.MDL.KernelStrictDescent where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Nat using (_<_; _≤_)

open import DASHI.MDL.MDLLyapunov
open import DASHI.Core.KernelOrbit

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record StrictKernelMDL
  {S : Set}
  (K : S → S)
  (M : MDLFunctional S) : Set₁ where
  field
    weak : MDLLyapunov K M
    strict-unless-fixed :
      ∀ s → K s ≢ s →
      MDLFunctional.mdl M (K s) < MDLFunctional.mdl M s
open StrictKernelMDL public

record StrictKernelQuotientMDL
  {S Q : Set}
  (q : S → Q)
  (K : S → S)
  (M : MDLFunctional S) : Set₁ where
  field
    weak : MDLLyapunov K M
    strict-unless-quotient-stable :
      ∀ s → q (K s) ≢ q s →
      MDLFunctional.mdl M (K s) < MDLFunctional.mdl M s
open StrictKernelQuotientMDL public

------------------------------------------------------------------------
-- Fail-closed finite-time certificates.
--
-- The existence of such a certificate is a theorem obligation for a concrete
-- finite state space or a concrete well-founded descent proof; it is not
-- silently postulated by the generic kernel interface.

record ReachesFixedPointWithin
  {S : Set}
  (K : S → S)
  (start : S)
  (fuel : Agda.Builtin.Nat.Nat) : Set where
  field
    time : Agda.Builtin.Nat.Nat
    time≤fuel : time ≤ fuel
    fixed-at-time : FixedPoint K (iterate time K start)
open ReachesFixedPointWithin public

record ReachesQuotientStableWithin
  {S Q : Set}
  (q : S → Q)
  (K : S → S)
  (start : S)
  (fuel : Agda.Builtin.Nat.Nat) : Set where
  field
    time : Agda.Builtin.Nat.Nat
    time≤fuel : time ≤ fuel
    stable-at-time : QuotientStable q K (iterate time K start)
open ReachesQuotientStableWithin public
