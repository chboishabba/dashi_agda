{-# OPTIONS --safe #-}
module DASHI.Core.ApproximateMultiscaleNaturality where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP

open import DASHI.Core.MultiscaleMDL

------------------------------------------------------------------------
-- A scale-indexed Nat-valued metric.  The existing 369 ultrametric is one
-- instance; analytic applications may supply norms or calibrated hybrid
-- distances separately.

record TowerMetric (tower : MultiscaleCarrier) : Set₁ where
  field
    distance : ∀ j → Carrier tower j → Carrier tower j → Nat
    self-zero : ∀ j (x : Carrier tower j) → distance j x x ≡ 0
    triangle :
      ∀ j (x y z : Carrier tower j) →
      distance j x z ≤ distance j x y + distance j y z
open TowerMetric public

record ApproximateKernelTower
  (tower : MultiscaleCarrier)
  (metric : TowerMetric tower) : Set₁ where
  field
    kernel≈ : ∀ j → Carrier tower j → Carrier tower j
    commutationError : ∀ {j} → Carrier tower (suc j) → Nat
    project-kernel-bound :
      ∀ {j} (x : Carrier tower (suc j)) →
      distance metric j
        (project tower (kernel≈ (suc j) x))
        (kernel≈ j (project tower x))
      ≤ commutationError x
open ApproximateKernelTower public

------------------------------------------------------------------------
-- Exact naturality embeds into approximate naturality with zero error.

exact-as-approximate :
  ∀ {tower} →
  (metric : TowerMetric tower) →
  KernelTower tower →
  ApproximateKernelTower tower metric
exact-as-approximate {tower} metric K =
  record
    { kernel≈ = kernel K
    ; commutationError = λ _ → 0
    ; project-kernel-bound = bound
    }
  where
    bound :
      ∀ {j} (x : Carrier tower (suc j)) →
      distance metric j
        (project tower (kernel K (suc j) x))
        (kernel K j (project tower x))
      ≤ 0
    bound {j} x rewrite project-kernel K x =
      NatP.≤-reflexive (self-zero metric j (kernel K j (project tower x)))

------------------------------------------------------------------------
-- Generic two-leg accumulation.  Repeated multiscale error control is built
-- by iterating this lemma; summability or vanishing of the resulting bound is
-- a separate analytic obligation.

accumulate-two-errors :
  ∀ {tower}
    (metric : TowerMetric tower)
    {j : Nat}
    (x y z : Carrier tower j)
    {e₁ e₂ : Nat} →
    distance metric j x y ≤ e₁ →
    distance metric j y z ≤ e₂ →
    distance metric j x z ≤ e₁ + e₂
accumulate-two-errors metric {j} x y z xy yz =
  NatP.≤-trans
    (triangle metric j x y z)
    (NatP.+-mono-≤ xy yz)

record ControlledErrorFamily
  {tower : MultiscaleCarrier}
  (metric : TowerMetric tower)
  (K : ApproximateKernelTower tower metric) : Set₁ where
  field
    globalBound : Nat → Nat
    pointwiseBound :
      ∀ {j} (x : Carrier tower (suc j)) →
      commutationError K x ≤ globalBound j
    tendsToZero : Set
    summable : Set
open ControlledErrorFamily public

-- `tendsToZero` and `summable` are proposition slots because their meaningful
-- definitions depend on the selected analytic number system and limit theory.
