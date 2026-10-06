module DASHI.NumberTheory.Collatz.SyracusePow2ArithmeticExact where

------------------------------------------------------------------------
-- SMALL POWER-OF-TWO ARITHMETIC SUPPORT
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (NonZero)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Foundations.Base369Nat as B369
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder

pow2IsSuccessor :
  (m : Nat) →
  Σ Nat (λ predecessor → Cylinder.pow2 m ≡ suc predecessor)
pow2IsSuccessor zero = zero , refl
pow2IsSuccessor (suc m) with pow2IsSuccessor m
... | predecessor , proof rewrite proof =
  suc (2 * predecessor) , refl

pow2NonZero : (m : Nat) → NonZero (Cylinder.pow2 m)
pow2NonZero m with pow2IsSuccessor m
... | predecessor , proof =
  subst NonZero (sym proof) B369.nonZero

record Pow2ArithmeticBoundary : Set where
  constructor pow2ArithmeticBoundary
  field
    successorShapeOwned : Nat
    nonZeroOwned : Nat

canonicalPow2ArithmeticBoundary : Pow2ArithmeticBoundary
canonicalPow2ArithmeticBoundary = pow2ArithmeticBoundary 1 1
