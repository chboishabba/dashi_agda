module DASHI.Geometry.Clifford.SpinFromSignature where

open import Data.Integer using (ℤ; _+_; _*_; +_)
open import Agda.Builtin.Equality using (_≡_)

-- Minimal bilinear form interface.
record BilinearForm : Set₁ where
  field
    V : Set
    g : V → V → ℤ

open BilinearForm public

-- Clifford algebra by generators/relations.
record Clifford (B : BilinearForm) : Set₁ where
  field
    Cl : Set
    one : Cl
    mul : Cl → Cl → Cl
    add : Cl → Cl → Cl
    embed : V B → Cl
    scalar : ℤ → Cl

    -- Clifford relation: vw + wv = 2 g(v,w) 1
    rel : ∀ v w →
      add (mul (embed v) (embed w))
          (mul (embed w) (embed v))
      ≡ scalar ((+ 2) * g B v w)

open Clifford public

-- Spin group as an abstract double cover of SO(3,1).
record SpinFromSignature : Set₂ where
  field
    B : BilinearForm
    Clif : Clifford B
    Spin : Set₁
    SO31 : Set₁
    cover : Spin → SO31
    doubleCover : Set

open SpinFromSignature public
