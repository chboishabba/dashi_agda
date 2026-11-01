module DASHI.Geometry.FixedPointExistence_Projection where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; sym)

open import DASHI.Algebra.MonsterMask15 using (Mask15; Kernel; projectTo)
open import DASHI.Algebra.MonsterUltrametric15 using (UMask15)
open import Ultrametric

Fixed : (Mask15 → Mask15) → Mask15 → Set
Fixed K m = K m ≡ m

iterate : (Mask15 → Mask15) → Nat → Mask15 → Mask15
iterate K zero    m = m
iterate K (suc n) m = iterate K n (K m)

-- For projection K = λ _ → target:
-- (1) target is a fixed point
fixed-target : ∀ target → Fixed (Kernel.K (projectTo target)) target
fixed-target target = refl

-- (2) unique fixed point
unique-fixed :
  ∀ target x y →
  Fixed (Kernel.K (projectTo target)) x →
  Fixed (Kernel.K (projectTo target)) y →
  x ≡ y
unique-fixed target x y fx fy = trans (sym fx) fy

-- (3) convergence in 1 step
converges-1 :
  ∀ target m → iterate (Kernel.K (projectTo target)) 1 m ≡ target
converges-1 target m = refl
