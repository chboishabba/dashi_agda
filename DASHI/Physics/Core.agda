{-# OPTIONS --safe #-}

module DASHI.Physics.Core where

open import Level using (Level; _⊔_; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; Σ; Σ-syntax; _,_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)

-- Abstract metric space; swap in your concrete ultrametric if desired.
record MetricSpace (ℓ : Level) : Set (suc ℓ) where
  field
    X     : Set ℓ
    d     : X → X → Set ℓ        -- use ℝ-valued distance later if needed
    reflD : ∀ x → d x x
    sym   : ∀ x y → d x y → d y x
    -- triangle etc as needed

-- Contractive operator skeleton.
record ContractionOp {ℓ : Level} (M : MetricSpace ℓ) : Set (suc (suc ℓ)) where
  open MetricSpace M
  field
    T      : X → X
    lam    : Set ℓ               -- typically a scalar 0<λ<1
    contractive : Set (suc ℓ)    -- replace with your inequality form

-- Bilinear and quadratic forms kept abstract.
record Bilinear {ℓ : Level} (V : Set ℓ) : Set (suc ℓ) where
  field
    B : V → V → Set ℓ

record Quadratic {ℓ : Level} (V : Set ℓ) : Set (suc ℓ) where
  field
    Q : V → Set ℓ

-- Involution / mirror.
record Involution {ℓ : Level} (V : Set ℓ) : Set (suc ℓ) where
  field
    ι    : V → V
    invol : ∀ v → ι (ι v) ≡ v

-- Finite speed / locality placeholder.
record FiniteSpeed {ℓ : Level} (V : Set ℓ) : Set (suc ℓ) where
  field
    locality : Set ℓ

-- Isotropy (rotation-like symmetries) and preservation of a quadratic form.
record Isotropy {ℓ : Level} (V : Set ℓ) : Set (suc ℓ) where
  field
    G   : Set ℓ
    act : G → V → V

record PreservesQuadratic {ℓ : Level} {V : Set ℓ} (iso : Isotropy V) (Q : Quadratic V) : Set (suc ℓ) where
  open Isotropy iso
  field
    pres : ∀ g v → Quadratic.Q Q (act g v) ≡ Quadratic.Q Q v

-- Clifford-like algebra interface via universal property.
record CliffordLike {ℓ : Level} (V : Set ℓ) : Set (suc ℓ) where
  field
    Cl    : Set ℓ
    embed : V → Cl
    -- relations to be added in DecimationToClifford

-- Even subalgebra carrier.
record EvenSubalg {ℓ : Level} (A : Set ℓ) : Set (suc ℓ) where
  field
    Even : Set ℓ
    inc  : Even → A
