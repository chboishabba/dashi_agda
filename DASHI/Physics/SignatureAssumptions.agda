module DASHI.Physics.SignatureAssumptions where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (_≤_; _<_)
open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.RealTernaryCarrier as RTC

------------------------------------------------------------------------
-- Quadratic invariant: a function Q preserved by an operator F

record QuadraticInvariant {A : Set} (Q : A → Nat) (F : A → A) : Set where
  field
    Q-invariant : ∀ x → Q (F x) ≡ Q x

------------------------------------------------------------------------
-- Indefinite signature (axiomatized)

record IndefiniteSignature {A : Set} (B : A → A → Nat) : Set₁ where
  field
    Q : A → Nat
    Q-def : ∀ x → Q x ≡ B x x
    sig : Nat × Nat

------------------------------------------------------------------------
-- Hyperbolic cone and orthogonality (schematic)

HyperbolicCone : {A : Set} → (Q : A → Nat) → A → Set
HyperbolicCone Q x = 0 < Q x

Orthogonal : {A : Set} → (B : A → A → Nat) → A → A → Set
Orthogonal B x y = B x y ≡ 0

------------------------------------------------------------------------
-- Dimension-bound seam lives in DimensionBoundAssumptions
