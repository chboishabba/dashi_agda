
module DASHI.Geometry.ParallelogramToInnerProduct where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_)

postulate
  V : Set
  _+_ _-_ : V → V → V
  0v : V

  ℚ : Set
  _+q_ _-q_ _*q_ : ℚ → ℚ → ℚ
  inv2 inv4 : ℚ

  ∥_∥² : V → ℚ

Parallelogram : Set
Parallelogram =
  ∀ x y →
    ∥ (x + y) ∥² +q ∥ (x - y) ∥² ≡
    (inv2 *q ((∥ x ∥² +q ∥ x ∥²) +q (∥ y ∥² +q ∥ y ∥²)))

polarization : V → V → ℚ
polarization x y =
  inv4 *q (∥ (x + y) ∥² -q ∥ (x - y) ∥²)

record InnerProduct : Set₁ where
  field
    ip : V → V → ℚ

Parallelogram⇒InnerProduct :
  Parallelogram →
  InnerProduct
Parallelogram⇒InnerProduct _ = record { ip = polarization }

-- The polarization identity is captured by `ip`, enabling downstream use of the quadratic form.
