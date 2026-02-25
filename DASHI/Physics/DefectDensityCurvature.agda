{-# OPTIONS --safe #-}
module DASHI.Physics.DefectDensityCurvature where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_)

record DefectField (S : Set) : Set₁ where
  field
    ρ : S → Nat
open DefectField public

record CurvatureField (S : Set) : Set₁ where
  field
    R : S → Nat
open CurvatureField public

record DefectToCurvature (S : Set) (D : DefectField S) (C : CurvatureField S) : Set₁ where
  field
    law : Set
