{-# OPTIONS --safe #-}
module DASHI.Instances.Primes where

record PrimeInstance : Set₁ where
  field
    S : Set
    T : S → S
