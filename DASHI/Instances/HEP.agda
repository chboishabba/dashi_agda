{-# OPTIONS --safe #-}
module DASHI.Instances.HEP where

open import Agda.Builtin.Sigma using (Σ; _,_)

record HEPInstance : Set₁ where
  field
    S : Set
    T : S → S
