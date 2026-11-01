{-# OPTIONS --safe #-}
module DASHI.MDL.CodeLengths where

open import Agda.Builtin.Nat using (Nat)

record CodeLengths (S : Set) : Set₁ where
  field
    L : S → Nat
    kraft : Set
open CodeLengths public
