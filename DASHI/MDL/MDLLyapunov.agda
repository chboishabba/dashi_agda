{-# OPTIONS --safe #-}
module DASHI.MDL.MDLLyapunov where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _+_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.MDL.CodeLengths

record MDLFunctional (S : Set) : Set₁ where
  field
    model residual : S → Nat
    mdl : S → Nat
    mdl≡ : ∀ s → mdl s ≡ model s + residual s
open MDLFunctional public

record MDLLyapunov {S : Set} (T : S → S) (M : MDLFunctional S) : Set₁ where
  open MDLFunctional M
  field
    decreases : ∀ s → MDLFunctional.mdl M (T s) ≤ MDLFunctional.mdl M s
    strictUnlessFixed : Set
open MDLLyapunov public
