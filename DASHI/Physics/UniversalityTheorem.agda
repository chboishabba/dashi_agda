{-# OPTIONS --safe #-}
module DASHI.Physics.UniversalityTheorem where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import DASHI.MDL.MDLLyapunov

record Universality : Set₁ where
  field
    statement : Set
