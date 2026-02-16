module MonsterProjection where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality
open import Data.Nat using (_<_)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Relation.Nullary

open import Ultrametric
open import MonsterMask
open import MonsterUltrametric

------------------------------------------------------------------------
-- Distinctness

_≢_ : Mask → Mask → Set
x ≢ y = ¬ (x ≡ y)

------------------------------------------------------------------------
-- Contractive on distinct points

record Contractive≢ (K : Mask → Mask) : Set where
  open Ultrametric.Ultrametric UMask
  field
    contraction≢ : ∀ {x y} → x ≢ y → d (K x) (K y) < d x y

------------------------------------------------------------------------
-- Projection to fixed mask is strictly contractive

postulate
  projContractive : ∀ target → Contractive≢ (Kernel.K (projectTo target))

------------------------------------------------------------------------
-- Fixed point definition

Fixed : (Mask → Mask) → Mask → Set
Fixed K m = K m ≡ m

------------------------------------------------------------------------
-- Unique fixed point for projection

uniqueFixedProj :
  ∀ target x y →
  Fixed (Kernel.K (projectTo target)) x →
  Fixed (Kernel.K (projectTo target)) y →
  x ≡ y
uniqueFixedProj target x y fx fy = trans (sym fx) fy
