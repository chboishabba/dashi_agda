module DASHI.NumberTheory.Collatz.SyracusePow2ArithmeticExact where

------------------------------------------------------------------------
-- SMALL POWER-OF-TWO ARITHMETIC SUPPORT
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_<_; z≤n; s≤s)
open import Data.Nat.Base using (NonZero; nonZero)
open import Data.Nat.DivMod using (_%_; _/_; m≡m%n+[m/n]*n; [m+kn]%n≡m%n)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

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

pow2Positive : (m : Nat) → 0 < Cylinder.pow2 m
pow2Positive m with pow2IsSuccessor m
... | predecessor , proof =
  subst (0 <_) (sym proof) (s≤s z≤n)

------------------------------------------------------------------------
-- Reducing modulo a nontrivial power of two preserves the final parity bit.
------------------------------------------------------------------------

instance
  nonZeroTwo : NonZero 2
  nonZeroTwo = nonZero

pow2RemainderPreservesModTwo :
  (m value : Nat) →
  (value % Cylinder.pow2 (suc m)) % 2 ≡ value % 2
pow2RemainderPreservesModTwo m value =
  let
    instance modulus-nonzero = pow2NonZero (suc m)
    modulus = Cylinder.pow2 (suc m)
    lower = Cylinder.pow2 m
    remainder = value % modulus
    quotient = value / modulus

    decomposition : value ≡ remainder + quotient * modulus
    decomposition = m≡m%n+[m/n]*n value modulus

    factorModulus :
      remainder + quotient * modulus
      ≡ remainder + (quotient * lower) * 2
    factorModulus =
      solve 3
        (λ r q M →
          r :+ q :* (con 2 :* M)
          :=
          r :+ (q :* M) :* con 2)
        refl remainder quotient lower

    projected :
      value % 2 ≡ remainder % 2
    projected =
      trans
        (cong (_% 2) decomposition)
        (trans
          (cong (_% 2) factorModulus)
          ([m+kn]%n≡m%n remainder (quotient * lower) 2))
  in
  sym projected

record Pow2ArithmeticBoundary : Set where
  constructor pow2ArithmeticBoundary
  field
    successorShapeOwned : Nat
    nonZeroOwned : Nat
    positivityOwned : Nat
    nestedModTwoProjectionOwned : Nat

canonicalPow2ArithmeticBoundary : Pow2ArithmeticBoundary
canonicalPow2ArithmeticBoundary = pow2ArithmeticBoundary 1 1 1 1
