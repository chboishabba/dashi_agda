{-# OPTIONS --safe #-}

module DASHI.Geometry.SignatureElimination where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Geometry.MaskedQuadratic

record OrbitProfile (V : Set) : Set₁ where
  field
    fp : V → List Nat

record SignatureLock {n : Nat} (V : Set) : Set₁ where
  field
    OP : OrbitProfile V
    eliminate : ∀ (MQ : MaskedQuadratic n) → Set  -- refine later

postulate
  Signature31FromLock :
    ∀ {n} {V} (MQ : MaskedQuadratic n) (L : SignatureLock {n} V) →
    SignatureLock.eliminate L MQ →
    MaskedQuadratic.signatureTag MQ ≡ sig31
